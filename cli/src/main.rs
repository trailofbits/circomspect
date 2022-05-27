use anyhow::{anyhow, Result};
use log::info;
use serde_json;
use std::convert::TryInto;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::str::FromStr;
use structopt::StructOpt;

use program_analysis::get_analysis_passes;
use program_structure::cfg::Cfg;
use program_structure::error_definition::MessageCategory;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::FileLibrary;
use program_structure::program_archive::ProgramArchive;
use program_structure::sarif_conversion::ToSarif;

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

const DEFAULT_VERSION: &str = "2.0.3";
const DEFAULT_LEVEL: &str = "warning";

#[derive(StructOpt)]
/// A static analyzer for Circom programs.
struct Cli {
    /// Initial input file
    #[structopt(name = "input")]
    input_file: String,

    /// Output level (either 'info', 'warning', or 'error')
    #[structopt(long, name = "level", default_value = DEFAULT_LEVEL)]
    output_level: Level,

    /// Sarif output file
    #[structopt(long, name = "output")]
    sarif_file: Option<PathBuf>,

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
) -> Result<(Cfg, ReportCollection)>
where
    T: TryInto<(Cfg, ReportCollection)>,
    T::Error: Into<Report>,
{
    let (mut cfg, reports) = ast.try_into().map_err(|error| {
        let reports = [error.into()];
        Report::print_reports(&reports, files);
        anyhow!("failed to generate CFG for '{name}'")
    })?;
    match cfg.into_ssa() {
        Ok(()) => Ok((cfg, reports)),
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
    let mut reports = ReportCollection::new();

    // Analyze all functions.
    for function in program.get_functions().values() {
        info!("analyzing function '{}'", function.get_name());
        let (cfg, mut new_reports) =
            generate_cfg(function, function.get_name(), &program.file_library)?;
        new_reports.extend(analyze_cfg(&cfg, &options.output_level));
        Report::print_reports(&new_reports, &program.file_library);
        reports.extend(new_reports);
    }
    // Analyze all templates.
    for template in program.get_templates().values() {
        info!("analyzing template '{}'", template.get_name());
        let (cfg, mut new_reports) =
            generate_cfg(template, template.get_name(), &program.file_library)?;
        new_reports.extend(analyze_cfg(&cfg, &options.output_level));
        Report::print_reports(&new_reports, &program.file_library);
        reports.extend(new_reports);
    }
    if let Some(sarif_path) = options.sarif_file {
        let sarif = reports.to_sarif(&program.file_library)?;
        let json = serde_json::to_string_pretty(&sarif)?;
        let mut sarif_file = File::create(sarif_path)?;
        writeln!(sarif_file, "{}", &json)?;
    }
    Ok(())
}
