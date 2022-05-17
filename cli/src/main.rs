use anyhow::{anyhow, Result};
use log::info;
use structopt::StructOpt;

use program_structure::error_definition::Report;
use program_structure::program_archive::ProgramArchive;
use program_structure::ssa::traits::DirectedGraphNode;

const CIRCOM_VERSION: &str = "2.0.3";

#[derive(StructOpt)]
/// Analyze Circom programs
struct CLI {
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

fn main() -> Result<()> {
    pretty_env_logger::init();
    let options = CLI::from_args();
    let program = parse_project(&options.input_file, options.compiler_version)?;

    for template in program.get_templates().values() {
        let mut cfg = match template.try_into() {
            Ok((cfg, warnings)) => {
                Report::print_reports(&warnings, &program.file_library);
                cfg
            }
            Err(error) => {
                let reports = [error.into()];
                Report::print_reports(&reports, &program.file_library);
                continue;
            }
        };
        match cfg.into_ssa() {
            Ok(()) => {}
            Err(error) => {
                let reports = [error.into()];
                Report::print_reports(&reports, &program.file_library);
                continue;
            }
        }
        for basic_block in cfg.iter() {
            info!("basic block {}:", basic_block.get_index());
            for stmt in basic_block.iter() {
                info!("    {stmt}");
            }
        }
    }
    Ok(())
}
