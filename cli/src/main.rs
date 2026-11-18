use std::path::PathBuf;
use std::process::ExitCode;
use std::num::NonZeroU64;
use std::time::Duration;
use clap::{CommandFactory, Parser};

use program_analysis::config;
use program_analysis::application::{analyze_files_with_observer, AnalysisTimeout, ApplicationError};
use program_structure::file_definition::FileLibrary;
use program_structure::report_code::ReportCode;

use program_structure::constants::Curve;
use program_structure::report::Report;
use program_structure::report::MessageCategory;
use program_structure::writers::{
    LogWriter, OutputPolicy, ReportWriter, ReportWriteError, SarifWriter, StdoutWriter,
};

mod live_output;
mod progress;
mod summary;

#[cfg(test)]
mod tests;

#[derive(Parser, Debug)]
#[command(styles=cli_styles())]
/// A static analyzer and linter for Circom programs.
struct Cli {
    /// Initial input file(s)
    #[clap(name = "INPUT")]
    input_files: Vec<PathBuf>,

    /// Ordered include search directories
    #[clap(short = 'L', long = "library", name = "LIBRARIES")]
    libraries: Vec<PathBuf>,

    /// Output level (INFO, WARNING, or ERROR)
    #[clap(short = 'l', long = "level", name = "LEVEL", default_value = config::DEFAULT_LEVEL)]
    output_level: MessageCategory,

    /// Output analysis results to a Sarif file
    #[clap(short, long, name = "OUTPUT")]
    sarif_file: Option<PathBuf>,

    /// Ignore results from given analysis passes
    #[clap(short = 'a', long = "allow", name = "ID")]
    allow_list: Vec<String>,

    /// Enable verbose output
    #[clap(short = 'v', long = "verbose")]
    verbose: bool,

    /// Set the curve used for field arithmetic.
    #[clap(short = 'c', long = "curve", name = "NAME", default_value = config::DEFAULT_CURVE,
        help = "Set curve (BN254, BLS12_381, or GOLDILOCKS)")]
    curve: Curve,

    /// Maximum analysis time per template/function context in seconds; omitted means unlimited.
    #[clap(long = "timeout", value_name = "SECONDS")]
    timeout: Option<NonZeroU64>,
}

/// Styles the help output for the [`Cli`].
fn cli_styles() -> clap::builder::Styles {
    use clap::builder::styling::{AnsiColor, Styles};

    Styles::styled()
        .header(AnsiColor::Yellow.on_default())
        .usage(AnsiColor::Green.on_default())
        .literal(AnsiColor::Green.on_default())
        .placeholder(AnsiColor::Green.on_default())
}

fn main() -> Result<ExitCode, String> {
    pretty_env_logger::init();
    let options = Cli::parse();
    if options.input_files.is_empty() {
        Cli::command()
            .print_help()
            .map_err(|error| format!("Cannot write help to stdout: {error}"))?;
        return Ok(ExitCode::SUCCESS);
    }

    run(options).map_err(|error| error.to_string())
}

fn analysis_timeout(seconds: Option<NonZeroU64>) -> AnalysisTimeout {
    match seconds {
        Some(seconds) => AnalysisTimeout::Bounded(Duration::from_secs(seconds.get())),
        None => AnalysisTimeout::Unlimited,
    }
}

fn run(options: Cli) -> Result<ExitCode, ReportWriteError> {
    let timeout = analysis_timeout(options.timeout);
    let ignored = options.allow_list.into_iter().collect();
    let mut stdout_writer = StdoutWriter::new(options.verbose);
    let output = match progress::report(options.verbose, |reporter| {
        let mut observer = live_output::LiveOutput::new(
            reporter,
            &mut stdout_writer,
            options.output_level,
            &ignored,
        );
        analyze_files_with_observer(
            &options.input_files,
            &options.libraries,
            options.curve,
            timeout,
            &mut observer,
        )
    }) {
        Ok(output) => output,
        Err(ApplicationError::Progress(error)) => return Err(ReportWriteError::Status(error)),
        Err(ApplicationError::Output(error)) => return Err(error),
        Err(error) => {
            let report =
                Report::error(format!("Analysis failed: {error}"), ReportCode::RuntimeError);
            stdout_writer.write_reports(&[report], &FileLibrary::new())?;
            return Ok(ExitCode::FAILURE);
        }
    };

    let policy =
        OutputPolicy::new(options.output_level, output.files.user_inputs().clone(), ignored);
    let mut reports = output.diagnostics;
    for scope in output.scopes {
        reports.extend(scope.reports);
    }

    if let Some(sarif_file) = options.sarif_file {
        let mut sarif_writer = SarifWriter::new(&sarif_file).add_filter(policy.clone());
        match sarif_writer.write_reports(&reports, &output.files) {
            Ok(count) if count > 0 => stdout_writer
                .write_message(format!("Result written to `{}`.", sarif_file.display()))?,
            Ok(_) => {}
            Err(error) => {
                let report = Report::error(
                    format!("Cannot write SARIF to {}: {error:#}", sarif_file.display()),
                    ReportCode::RuntimeError,
                );
                stdout_writer.write_reports(&[report], &output.files)?;
                return Ok(ExitCode::FAILURE);
            }
        }
    }

    stdout_writer.write_message(summary::describe(&reports, &policy))?;
    Ok(if stdout_writer.reports_written() == 0 && summary::timeout_count(&reports) == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}
