use anyhow::{anyhow, Result};
use clap::Parser;
use log::info;
use parser::ParseResult;
use program_structure::function_data::FunctionInfo;
use program_structure::template_data::TemplateInfo;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::str::FromStr;

use program_analysis::get_analysis_passes;
use program_structure::cfg::Cfg;
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

const DEFAULT_VERSION: &str = "2.0.3";
const DEFAULT_LEVEL: &str = "WARNING";

#[derive(StructOpt)]
/// A static analyzer for Circom programs.
struct Cli {
    /// Initial input file
    #[structopt(name = "input")]
    input_file: String,

    /// Output level (either INFO, WARNING, or ERROR)
    #[structopt(long, name = "level", default_value = DEFAULT_LEVEL)]
    output_level: Level,

    /// Output analysis results to a Sarif file
    #[structopt(long, name = "output")]
    sarif_file: Option<PathBuf>,

    /// Expected compiler version
    #[structopt(long, name = "version", default_value = DEFAULT_VERSION)]
    compiler_version: String,
}

fn generate_cfg<T: TryInto<(Cfg, ReportCollection)>>(
    ast: T,
) -> Result<(Cfg, ReportCollection), ReportCollection>
where
    T: TryInto<(Cfg, ReportCollection)>,
    T::Error: Into<Report>,
{
    let (cfg, reports) = ast.try_into().map_err(|error| vec![error.into()])?;
    match cfg.into_ssa() {
        Ok(cfg) => Ok((cfg, reports)),
        Err(error) => Err(vec![error.into()]),
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

fn analyze_definitions(
    functions: &FunctionInfo,
    templates: &TemplateInfo,
    file_library: &FileLibrary,
    output_level: &Level,
) -> ReportCollection {
    let mut reports = Vec::new();

    // Analyze all functions.
    for (name, function) in functions {
        info!("analyzing function '{name}'");
        let (cfg, mut new_reports) = match generate_cfg(function) {
            Ok((cfg, warnings)) => (cfg, warnings),
            Err(errors) => return errors,
        };
        new_reports.extend(analyze_cfg(&cfg, output_level));
        Report::print_reports(&new_reports, file_library);
        reports.extend(new_reports);
    }
    // Analyze all templates.
    for (name, template) in templates {
        info!("analyzing template '{name}'");
        let (cfg, mut new_reports) = match generate_cfg(template) {
            Ok((cfg, warnings)) => (cfg, warnings),
            Err(errors) => return errors,
        };
        new_reports.extend(analyze_cfg(&cfg, output_level));
        Report::print_reports(&new_reports, file_library);
        reports.extend(new_reports);
    }
    reports
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
    let mut reports = ReportCollection::new();

    let file_library = match parser::parse_files(&options.input_file, &options.compiler_version) {
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
        // Analyze a set of Circom definitions.
        ParseResult::Library(library, mut errors) => {
            Report::print_reports(&reports, &library.file_library);
            reports.append(&mut errors);
            reports.append(&mut analyze_definitions(
                &library.functions,
                &library.templates,
                &library.file_library,
                &options.output_level,
            ));
            library.file_library
        }
    };

    if let Some(sarif_path) = options.sarif_file {
        let sarif = reports.to_sarif(&file_library)?;
        let json = serde_json::to_string_pretty(&sarif)?;
        let mut sarif_file = File::create(sarif_path)?;
        writeln!(sarif_file, "{}", &json)?;
    }
    Ok(())
}
