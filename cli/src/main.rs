use std::path::PathBuf;
use std::process::ExitCode;
use clap::{CommandFactory, Parser};

use program_analysis::config;
use program_analysis::application::analyze_files;
use program_structure::file_definition::FileLibrary;
use program_structure::report_code::ReportCode;

use program_structure::constants::Curve;
use program_structure::report::Report;
use program_structure::report::MessageCategory;
use program_structure::writers::{
    LogWriter, OutputPolicy, ReportWriter, ReportWriteError, SarifWriter, CachedStdoutWriter,
};

#[cfg(test)]
mod tests;

#[derive(Parser, Debug)]
#[command(styles=cli_styles())]
/// A static analyzer and linter for Circom programs.
struct Cli {
    /// Initial input file(s)
    #[clap(name = "INPUT")]
    input_files: Vec<PathBuf>,

    /// Library file paths
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
    // Initialize logger and options.
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

fn run(options: Cli) -> Result<ExitCode, ReportWriteError> {
    let output = match analyze_files(&options.input_files, &options.libraries, options.curve) {
        Ok(output) => output,
        Err(error) => {
            let report =
                Report::error(format!("Analysis failed: {error}"), ReportCode::RuntimeError);
            CachedStdoutWriter::new(options.verbose)
                .write_reports(&[report], &FileLibrary::new())?;
            return Ok(ExitCode::FAILURE);
        }
    };

    // Set up writer and write reports to `stdout`.
    let policy = OutputPolicy::new(
        options.output_level,
        output.files.user_inputs().clone(),
        options.allow_list.into_iter().collect(),
    );
    let mut stdout_writer = CachedStdoutWriter::new(options.verbose).add_filter(policy.clone());
    stdout_writer.write_reports(&output.diagnostics, &output.files)?;

    // Render completed function and template analyses in input order.
    for scope in &output.scopes {
        stdout_writer.write_message(format!("analyzing {}", scope.description))?;
        stdout_writer.write_reports(&scope.reports, &output.files)?;
    }

    // If a Sarif file is passed to the program we write the reports to it.
    if let Some(sarif_file) = options.sarif_file {
        let mut sarif_writer = SarifWriter::new(&sarif_file).add_filter(policy);
        match sarif_writer.write_reports(stdout_writer.reports(), &output.files) {
            Ok(count) if count > 0 => stdout_writer
                .write_message(format!("Result written to `{}`.", sarif_file.display()))?,
            Ok(_) => {}
            Err(error) => {
                let report = Report::error(
                    format!("Cannot write SARIF to {}: {error:#}", sarif_file.display()),
                    ReportCode::RuntimeError,
                );
                CachedStdoutWriter::new(options.verbose).write_reports(&[report], &output.files)?;
                return Ok(ExitCode::FAILURE);
            }
        }
    }

    // Use the exit code to indicate if any issues were found.
    Ok(match stdout_writer.reports_written() {
        0 => {
            stdout_writer.write_message("No issues found.")?;
            ExitCode::SUCCESS
        }
        1 => {
            stdout_writer.write_message("1 issue found.")?;
            ExitCode::FAILURE
        }
        n => {
            stdout_writer.write_message(format!("{n} issues found."))?;
            ExitCode::FAILURE
        }
    })
}
