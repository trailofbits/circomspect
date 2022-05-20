use anyhow::{anyhow, Result};
use log::info;
use std::convert::TryInto;
use std::str::FromStr;
use structopt::StructOpt;

use program_structure::cfg::Cfg;
use program_structure::error_definition::MessageCategory;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::FileLibrary;
use program_structure::program_archive::ProgramArchive;

use program_analysis::get_analysis_passes;

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

pub enum Format {
    Log,
    Sarif,
}

impl FromStr for Format {
    type Err = anyhow::Error;

    fn from_str(format: &str) -> Result<Format, Self::Err> {
        match format.to_lowercase().as_str() {
            "log" | "warning" => Ok(Format::Log),
            "sarif" => Ok(Format::Sarif),
            _ => Err(anyhow!("failed to parse format '{format}'")),
        }
    }
}

const DEFAULT_VERSION: &str = "2.0.3";
const DEFAULT_FORMAT: &str = "log";
const DEFAULT_LEVEL: &str = "warning";

#[derive(StructOpt)]
/// Analyze Circom programs
struct Cli {
    /// Initial input file
    #[structopt(name = "input")]
    input_file: String,

    /// Output level (either 'info', 'warning', or 'error')
    #[structopt(long, name = "level", default_value = DEFAULT_LEVEL)]
    output_level: Level,

    /// Output format (either 'log' or 'sarif')
    #[structopt(long, name = "format", default_value = DEFAULT_FORMAT)]
    output_format: Format,

    /// Expected compiler version
    #[structopt(long, name = "version", default_value = DEFAULT_VERSION)]
    compiler_version: String,
}

fn parse_project(initial_file: &str, compiler_version: &str) -> Result<ProgramArchive> {
    match parser::run_parser(initial_file.to_string(), compiler_version) {
        Ok((program, warnings)) => {
            Report::print_reports(&warnings, &program.file_library);
            Ok(program)
        }
        Err((files, errors)) => {
            Report::print_reports(&errors, &files);
            Err(anyhow!("failed to parse {}", initial_file))
        }
    }
}

fn generate_cfg<T: TryInto<(Cfg, ReportCollection)>>(
    ast: T,
    name: &str,
    files: &FileLibrary,
) -> Result<Cfg>
where
    T: TryInto<(Cfg, ReportCollection)>,
    T::Error: Into<Report>,
{
    let mut cfg = match ast.try_into() {
        Ok((cfg, warnings)) => {
            Report::print_reports(&warnings, files);
            cfg
        }
        Err(error) => {
            let reports = [error.into()];
            Report::print_reports(&reports, files);
            return Err(anyhow!("failed to generate CFG for '{name}'"));
        }
    };
    match cfg.into_ssa() {
        Ok(()) => Ok(cfg),
        Err(error) => {
            let reports = [error.into()];
            Report::print_reports(&reports, files);
            Err(anyhow!("failed to convert '{name}' to SSA"))
        }
    }
}

fn analyze_cfg(cfg: &Cfg, output_level: &Level) -> ReportCollection {
    let mut reports = ReportCollection::new();
    for analysis_pass in get_analysis_passes() {
        reports.extend(analysis_pass(cfg));
    }
    reports
        .iter()
        .filter(|report| filter_by_level(report, output_level))
        .cloned()
        .collect()
}

fn filter_by_level(report: &Report, output_level: &Level) -> bool {
    use MessageCategory::*;
    match output_level {
        Level::Info => matches!(report.get_category(), Info | Warning | Error),
        Level::Warning => matches!(report.get_category(), Warning | Error),
        Level::Error => matches!(report.get_category(), Error),
    }
}

fn main() -> Result<()> {
    pretty_env_logger::init();
    let options = Cli::from_args();
    let program = parse_project(&options.input_file, &options.compiler_version)?;

    for function in program.get_functions().values() {
        info!("analyzing function '{}'", function.get_name());
        let cfg = generate_cfg(function, function.get_name(), &program.file_library)?;
        let reports = analyze_cfg(&cfg, &options.output_level);
        Report::print_reports(&reports, &program.file_library);
    }
    for template in program.get_templates().values() {
        info!("analyzing template '{}'", template.get_name());
        let cfg = generate_cfg(template, template.get_name(), &program.file_library)?;
        let reports = analyze_cfg(&cfg, &options.output_level);
        Report::print_reports(&reports, &program.file_library);
    }
    Ok(())
}
