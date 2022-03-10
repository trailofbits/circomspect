use anyhow::{anyhow, Result};
use log::info;
use pretty_env_logger;
use structopt::StructOpt;

use parser;
use program_analysis::shadowing_analysis::ShadowingAnalysis;
use program_structure::error_definition::Report;
use program_structure::program_archive::ProgramArchive;

const CIRCOM_VERSION: &str = "2.0.3";

#[derive(StructOpt)]
/// Analyze Circom programs
struct CLI {
    /// Initial iput file
    #[structopt(name = "input")]
    input_file: String,

    /// Output file (defaults to stdout)
    #[structopt(name = "output")]
    output_file: Option<String>,

    /// Expected compiler version
    #[structopt(long, short)]
    compiler_version: Option<String>,
}

fn parse_project(
    initial_file: &str,
    compiler_version: Option<String>,
) -> Result<ProgramArchive> {
    let compiler_version = &compiler_version.unwrap_or(CIRCOM_VERSION.to_string());
    match parser::run_parser(initial_file.to_string(), compiler_version) {
        Result::Err((files, reports)) => {
            Report::print_reports(&reports, &files);
            Err(anyhow!("failed to parse {}", initial_file))
        }
        Result::Ok((program, warnings)) => {
            Report::print_reports(&warnings, &program.file_library);
            Ok(program)
        }
    }
}

fn main() -> Result<()> {
    pretty_env_logger::init();
    let options = CLI::from_args();
    let program = parse_project(&options.input_file, options.compiler_version)?;

    let mut analysis = ShadowingAnalysis::new();
    let reports = analysis.run(&program);
    Report::print_reports(&reports, &program.file_library);
    Ok(())
}
