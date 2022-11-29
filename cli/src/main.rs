use anyhow::Result;
use clap::{CommandFactory, Parser};
use parser::ParseResult;
use program_structure::constants::Curve;
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

use program_analysis::get_analysis_passes;
use program_structure::cfg::{Cfg, IntoCfg};
use program_structure::report::MessageCategory;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::FileLibrary;
use program_structure::function_data::FunctionInfo;
use program_structure::report_writer::{StdoutWriter, ReportWriter, SarifWriter};
use program_structure::template_data::TemplateInfo;

const COMPILER_VERSION: &str = "2.0.8";
const DEFAULT_LEVEL: &str = "WARNING";
const DEFAULT_CURVE: &str = "BN128";

#[derive(Parser, Debug)]
/// A static analyzer and linter for Circom programs.
struct Cli {
    /// Initial input file(s)
    #[clap(name = "INPUT")]
    input_files: Vec<PathBuf>,

    /// Output level (INFO, WARNING, or ERROR)
    #[clap(short = 'l', long = "level", name = "LEVEL", default_value = DEFAULT_LEVEL)]
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
    #[clap(short = 'c', long = "curve", name = "NAME", default_value = DEFAULT_CURVE)]
    curve: Curve,
}

fn generate_cfg<Ast: IntoCfg>(
    ast: Ast,
    curve: &Curve,
    reports: &mut ReportCollection,
) -> Result<Cfg, Box<Report>> {
    ast.into_cfg(curve, reports)
        .map_err(|error| Box::new(Report::from(error)))?
        .into_ssa()
        .map_err(|error| Box::new(Report::from(error)))
}

fn analyze_cfg(cfg: &Cfg, reports: &mut ReportCollection) {
    for analysis_pass in get_analysis_passes() {
        reports.extend(analysis_pass(cfg));
    }
}

fn analyze_ast<Ast: IntoCfg>(ast: Ast, curve: &Curve, reports: &mut ReportCollection) {
    match generate_cfg(ast, curve, reports) {
        Ok(cfg) => {
            analyze_cfg(&cfg, reports);
        }
        Err(error) => {
            reports.push(*error);
        }
    };
}

fn analyze_definitions(
    functions: &FunctionInfo,
    templates: &TemplateInfo,
    file_library: &FileLibrary,
    curve: &Curve,
    writer: &mut StdoutWriter,
) -> ReportCollection {
    let mut all_reports = ReportCollection::new();

    // Analyze all functions.
    for (name, function) in functions {
        log_message(&format!("analyzing function '{name}'"));
        let mut new_reports = ReportCollection::new();
        analyze_ast(function, curve, &mut new_reports);
        writer.write(&new_reports, file_library);
        all_reports.extend(new_reports);
    }
    // Analyze all templates.
    for (name, template) in templates {
        log_message(&format!("analyzing template '{name}'"));
        let mut new_reports = ReportCollection::new();
        analyze_ast(template, curve, &mut new_reports);
        writer.write(&new_reports, file_library);
        all_reports.extend(new_reports);
    }
    all_reports
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

fn log_message(message: &str) {
    let mut writer = if atty::is(atty::Stream::Stdout) {
        StandardStream::stdout(ColorChoice::Always)
    } else {
        StandardStream::stdout(ColorChoice::Never)
    };
    // We ignore logging failures.
    let _ = writer.set_color(ColorSpec::new().set_fg(Some(Color::Green)));
    let _ = write!(&mut writer, "circomspect");
    let _ = writer.reset();
    let _ = writeln!(&mut writer, ": {message}");
}

fn main() -> ExitCode {
    pretty_env_logger::init();
    let options = Cli::parse();
    if options.input_files.is_empty() {
        match Cli::command().print_help() {
            Ok(()) => return ExitCode::SUCCESS,
            Err(_) => return ExitCode::FAILURE,
        }
    }
    let mut reports = ReportCollection::new();
    let allow_list = options.allow_list.clone();
    let output_level = options.output_level;
    let mut writer = StdoutWriter::new(options.verbose)
        .add_filter(move |report: &Report| filter_by_id(report, &allow_list))
        .add_filter(move |report: &Report| filter_by_level(report, &output_level));

    let file_library = match parser::parse_files(&options.input_files, COMPILER_VERSION) {
        // Analyze a complete Circom program.
        ParseResult::Program(program, mut warnings) => {
            writer.write(&warnings, &program.file_library);
            reports.append(&mut warnings);
            reports.append(&mut analyze_definitions(
                &program.functions,
                &program.templates,
                &program.file_library,
                &options.curve,
                &mut writer,
            ));
            program.file_library
        }
        // Analyze a set of Circom template files.
        ParseResult::Library(library, mut warnings) => {
            writer.write(&warnings, &library.file_library);
            reports.append(&mut warnings);
            reports.append(&mut analyze_definitions(
                &library.functions,
                &library.templates,
                &library.file_library,
                &options.curve,
                &mut writer,
            ));
            library.file_library
        }
    };
    // If a Sarif file is passed to the program we write the reports to it.
    if let Some(sarif_file) = options.sarif_file {
        let allow_list = options.allow_list.clone();
        let output_level = options.output_level;
        let mut writer = SarifWriter::new(&sarif_file)
            .add_filter(move |report: &Report| filter_by_id(report, &allow_list))
            .add_filter(move |report: &Report| filter_by_level(report, &output_level));
        if writer.write(&reports, &file_library) > 0 {
            log_message(&format!("Result written to `{}`.", sarif_file.display()));
        }
    }
    // Use the exit code to indicate if any issues were found.
    match writer.written() {
        0 => {
            log_message("No issues found.");
            ExitCode::SUCCESS
        }
        1 => {
            log_message("1 issue found.");
            ExitCode::FAILURE
        }
        n => {
            log_message(&format!("{n} issues found."));
            ExitCode::FAILURE
        }
    }
}
