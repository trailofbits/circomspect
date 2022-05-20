use log::info;
use anyhow::{anyhow, Result};
use program_structure::file_definition::FileLibrary;
use structopt::StructOpt;
use std::convert::TryInto;

use program_structure::cfg::Cfg;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::program_archive::ProgramArchive;
use program_analysis::get_analysis_passes;

const CIRCOM_VERSION: &str = "2.0.3";

#[derive(StructOpt)]
/// Analyze Circom programs
struct Cli {
    /// Initial input file
    #[structopt(name = "input")]
    input_file: String,

    /// Output to file (defaults to stdout)
    #[structopt(name = "output")]
    output_file: Option<String>,

    /// Output format (defaults to logging)
    output_format: Option<String>,

    /// Expected compiler version
    #[structopt(long, short)]
    compiler_version: Option<String>,
}

fn parse_project(initial_file: &str, compiler_version: Option<String>) -> Result<ProgramArchive> {
    let compiler_version = &compiler_version.unwrap_or(CIRCOM_VERSION.to_string());
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
) -> Result<Cfg>
where
    T: TryInto<(Cfg, ReportCollection)>,
    T::Error: Into<Report>
{
    let mut cfg = match ast.try_into() {
        Ok((cfg, warnings)) => {
            Report::print_reports(&warnings, &files);
            cfg
        }
        Err(error) => {
            let reports = [error.into()];
            Report::print_reports(&reports, &files);
            return Err(anyhow!("failed to generate CFG for '{name}'"));
        }
    };
    match cfg.into_ssa() {
        Ok(()) => Ok(cfg),
        Err(error) => {
            let reports = [error.into()];
            Report::print_reports(&reports, &files);
            Err(anyhow!("failed to convert '{name}' to SSA"))
        }
    }
}

fn analyze_cfg(cfg: &Cfg, output_level: &Level) -> ReportCollection {
    let mut reports = ReportCollection::new();
    for analysis_pass in get_analysis_passes() {
        reports.extend(analysis_pass(&cfg));
    }
    reports
}

fn main() -> Result<()> {
    pretty_env_logger::init();
    let options = Cli::from_args();
    let program = parse_project(&options.input_file, options.compiler_version)?;

    for function in program.get_functions().values() {
        info!("analyzing function '{}'", function.get_name());
        let cfg = generate_cfg(function, function.get_name(), &program.file_library)?;
        let reports = analyze_cfg(&cfg);
        Report::print_reports(&reports, &program.file_library);
    }
    for template in program.get_templates().values() {
        info!("analyzing template '{}'", template.get_name());
        let cfg = generate_cfg(template, template.get_name(), &program.file_library)?;
        let reports = analyze_cfg(&cfg);
        Report::print_reports(&reports, &program.file_library);
    }
    Ok(())
}
