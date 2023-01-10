use std::path::PathBuf;
use std::process::ExitCode;
use clap::{CommandFactory, Parser};

use program_analysis::config;
use program_analysis::analysis_runner::AnalysisRunner;

use program_structure::constants::Curve;
use program_structure::report::Report;
use program_structure::report::MessageCategory;
use program_structure::writers::{LogWriter, ReportWriter, SarifWriter, CachedStdoutWriter};

#[derive(Parser, Debug)]
/// A static analyzer and linter for Circom programs.
struct Cli {
    /// Initial input file(s)
    #[clap(name = "INPUT")]
    input_files: Vec<PathBuf>,

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

    /// Set curve (BN128, BLS12_381, or GOLDILOCKS)
    #[clap(short = 'c', long = "curve", name = "NAME", default_value = config::DEFAULT_CURVE)]
    curve: Curve,
}

/// Returns true if the report level is greater than or equal to the given
/// level.
fn filter_by_level(report: &Report, output_level: &MessageCategory) -> bool {
    report.category() >= output_level
}

/// Returns true if the report ID is not in the given list.
fn filter_by_id(report: &Report, allow_list: &[String]) -> bool {
    !allow_list.contains(&report.id())
}

fn main() -> ExitCode {
    // Initialize logger and options.
    pretty_env_logger::init();
    let options = Cli::parse();
    if options.input_files.is_empty() {
        match Cli::command().print_help() {
            Ok(()) => return ExitCode::SUCCESS,
            Err(_) => return ExitCode::FAILURE,
        }
    }

    // Set up analysis runner and analyze all functions and templates.
    let allow_list = options.allow_list.clone();
    let mut stdout_writer = CachedStdoutWriter::new(options.verbose)
        .add_filter(move |report: &Report| filter_by_id(report, &allow_list))
        .add_filter(move |report: &Report| filter_by_level(report, &options.output_level));
    let mut runner = AnalysisRunner::new(&options.curve);
    runner.with_files(&options.input_files, &mut stdout_writer);

    runner.analyze_functions(&mut stdout_writer);
    runner.analyze_templates(&mut stdout_writer);

    // If a Sarif file is passed to the program we write the reports to it.
    if let Some(sarif_file) = options.sarif_file {
        let allow_list = options.allow_list.clone();
        let mut sarif_writer = SarifWriter::new(&sarif_file)
            .add_filter(move |report: &Report| filter_by_id(report, &allow_list))
            .add_filter(move |report: &Report| filter_by_level(report, &options.output_level));
        if sarif_writer.write_reports(stdout_writer.reports(), runner.file_library()) > 0 {
            stdout_writer.write_message(&format!("Result written to `{}`.", sarif_file.display()));
        }
    }

    // Use the exit code to indicate if any issues were found.
    match stdout_writer.reports_written() {
        0 => {
            stdout_writer.write_message("No issues found.");
            ExitCode::SUCCESS
        }
        1 => {
            stdout_writer.write_message("1 issue found.");
            ExitCode::FAILURE
        }
        n => {
            stdout_writer.write_message(&format!("{n} issues found."));
            ExitCode::FAILURE
        }
    }
}
