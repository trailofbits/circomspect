use anyhow::{anyhow, Result};
use clap::{CommandFactory, Parser};
use log::{info, error};
use parser::ParseResult;
use program_structure::function_data::FunctionInfo;
use program_structure::template_data::TemplateInfo;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::str::FromStr;
use std::process::ExitCode;

use program_analysis::get_analysis_passes;
use program_structure::cfg::{Cfg, IntoCfg};
use program_structure::error_definition::MessageCategory;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::FileLibrary;
use program_structure::sarif_conversion::ToSarif;

#[derive(Debug)]
pub enum Level {
    Info,
    Warning,
    Error,
}

impl FromStr for Level {
    type Err = anyhow::Error;

    fn from_str(level: &str) -> Result<Level, Self::Err> {
        match level.to_lowercase().as_str() {
            "warn" | "warning" => Ok(Level::Warning),
            "info" => Ok(Level::Info),
            "error" => Ok(Level::Error),
            _ => Err(anyhow!("failed to parse level '{level}'")),
        }
    }
}

const COMPILER_VERSION: &str = "2.0.3";
const DEFAULT_LEVEL: &str = "WARNING";

#[derive(Parser, Debug)]
/// A static analyzer for Circom programs.
struct Cli {
    /// Initial input file(s)
    #[clap(name = "INPUT")]
    input_files: Vec<PathBuf>,

    /// Output level (INFO, WARNING, or ERROR)
    #[clap(short = 'l', long, name = "LEVEL", default_value = DEFAULT_LEVEL)]
    output_level: Level,

    /// Output analysis results to a Sarif file
    #[clap(short, long, name = "OUTPUT")]
    sarif_file: Option<PathBuf>,
}

fn generate_cfg<Ast: IntoCfg>(ast: Ast, reports: &mut ReportCollection) -> Result<Cfg, Report> {
    ast.into_cfg(reports)
        .map_err(Into::<Report>::into)?
        .into_ssa()
        .map_err(Into::<Report>::into)
}

fn analyze_cfg(cfg: &Cfg, reports: &mut ReportCollection) {
    for analysis_pass in get_analysis_passes() {
        reports.extend(analysis_pass(cfg));
    }
}

fn analyze_ast<Ast: IntoCfg>(ast: Ast, reports: &mut ReportCollection) {
    match generate_cfg(ast, reports) {
        Ok(cfg) => {
            analyze_cfg(&cfg, reports);
        }
        Err(error) => {
            reports.push(error);
        }
    };
}

fn analyze_definitions(
    functions: &FunctionInfo,
    templates: &TemplateInfo,
    file_library: &FileLibrary,
    output_level: &Level,
) -> ReportCollection {
    let mut all_reports = ReportCollection::new();

    // Analyze all functions.
    for (name, function) in functions {
        info!("analyzing function '{name}'");
        let mut new_reports = ReportCollection::new();
        analyze_ast(function, &mut new_reports);
        filter_reports(&mut new_reports, output_level);
        Report::print_reports(&new_reports, file_library);
        all_reports.extend(new_reports);
    }
    // Analyze all templates.
    for (name, template) in templates {
        info!("analyzing template '{name}'");
        let mut new_reports = ReportCollection::new();
        analyze_ast(template, &mut new_reports);
        filter_reports(&mut new_reports, output_level);
        Report::print_reports(&new_reports, file_library);
        all_reports.extend(new_reports);
    }
    all_reports
}

fn filter_reports(reports: &mut ReportCollection, output_level: &Level) {
    *reports = reports
        .iter()
        .filter(|report| filter_by_level(report, output_level))
        .cloned()
        .collect();
}

fn filter_by_level(report: &Report, output_level: &Level) -> bool {
    use MessageCategory::*;
    match output_level {
        Level::Info => matches!(report.get_category(), Info | Warning | Error),
        Level::Warning => matches!(report.get_category(), Warning | Error),
        Level::Error => matches!(report.get_category(), Error),
    }
}

fn serialize_reports(sarif_path: &PathBuf, reports: &ReportCollection, file_library: &FileLibrary) -> Result<()> {
    let sarif = reports.to_sarif(file_library)?;
    let json = serde_json::to_string_pretty(&sarif)?;
    let mut sarif_file = File::create(sarif_path)?;
    writeln!(sarif_file, "{}", &json)?;
    Ok(())
}

fn main() -> ExitCode {
    pretty_env_logger::init();
    let options = Cli::from_args();
    if options.input_files.is_empty() {
        match Cli::command().print_help() {
            Ok(()) => return ExitCode::SUCCESS,
            Err(_) => return ExitCode::FAILURE,
        }
    }

    let mut reports = ReportCollection::new();
    let file_library = match parser::parse_files(&options.input_files, COMPILER_VERSION) {
        // Analyze a complete Circom program.
        ParseResult::Program(program, mut warnings) => {
            Report::print_reports(&warnings, &program.file_library);
            reports.append(&mut warnings);
            reports.append(&mut analyze_definitions(
                &program.functions,
                &program.templates,
                &program.file_library,
                &options.output_level,
            ));
            program.file_library
        }
        // Analyze a set of Circom template files.
        ParseResult::Library(library, mut warnings) => {
            Report::print_reports(&warnings, &library.file_library);
            reports.append(&mut warnings);
            reports.append(&mut analyze_definitions(
                &library.functions,
                &library.templates,
                &library.file_library,
                &options.output_level,
            ));
            library.file_library
        }
    };
    // If a Sarif file is passed to the program we write the reports to it.
    if let Some(sarif_path) = options.sarif_file {
        match serialize_reports(&sarif_path, &reports, &file_library) {
            Ok(()) => info!("reports written to `{}`", sarif_path.display()),
            Err(_) => error!("failed to write reports to `{}`", sarif_path.display()),
        }
    }
    // Use the exit code to indicate if any issues were found.
    if reports.is_empty() {
        println!("No issues found.");
        ExitCode::SUCCESS
    } else {
        if reports.len() == 1 {
            println!("{} issue found.", reports.len());
        } else {
            println!("{} issues found.", reports.len());
        }
        ExitCode::FAILURE
    }
}
