extern crate num_bigint_dig as num_bigint;
extern crate num_traits;
extern crate serde;
extern crate serde_derive;
#[macro_use]
extern crate lalrpop_util;

lalrpop_mod!(pub lang);

mod errors;
mod include_logic;
mod parser_logic;
use include_logic::FileStack;
use program_structure::ast::{Version, AST};
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::program_archive::ProgramArchive;
use program_structure::template_library::TemplateLibrary;
use std::collections::HashMap;
use std::path::PathBuf;
use std::str::FromStr;

pub enum ParseResult {
    // The program was successfully parsed without issues.
    Program(ProgramArchive, ReportCollection),
    // The parser failed to parse a complete program.
    Library(TemplateLibrary, ReportCollection),
}

fn parse_file(
    file_path: &PathBuf,
    file_stack: &mut FileStack,
    file_library: &mut FileLibrary,
    compiler_version: &Version,
) -> Result<(FileID, AST, ReportCollection), Report> {
    let (path_str, file_content) = open_file(file_path)?;
    let file_id = file_library.add_file(path_str, file_content.clone());
    let program = parser_logic::parse_file(&file_content, file_id)?;
    for include in &program.includes {
        // TODO: This will fail on the first invalid include statement.
        FileStack::add_include(file_stack, include.clone())?;
    }
    let warnings = check_compiler_version(file_path, program.compiler_version, compiler_version)?;
    Ok((file_id, program, warnings))
}

pub fn parse_files(file_paths: &Vec<PathBuf>, compiler_version: &str) -> ParseResult {
    let compiler_version = parse_version_string(compiler_version);

    let mut file_stack = FileStack::new(file_paths);
    let mut file_library = FileLibrary::new();
    let mut definitions = HashMap::new();
    let mut main_components = Vec::new();
    let mut reports = Vec::new();
    while let Some(file_path) = FileStack::take_next(&mut file_stack) {
        match parse_file(
            &file_path,
            &mut file_stack,
            &mut file_library,
            &compiler_version,
        ) {
            Ok((file_id, program, mut warnings)) => {
                if let Some(main_component) = program.main_component {
                    main_components.push((file_id, main_component));
                }
                definitions.insert(file_id, program.definitions);
                reports.append(&mut warnings);
            }
            Err(error) => {
                reports.push(error);
            }
        }
    }
    match &main_components[..] {
        [(main_id, main_component)] => {
            // TODO: This calls FillMeta::fill a second time.
            match ProgramArchive::new(file_library, *main_id, main_component, &definitions) {
                Ok(program_archive) => ParseResult::Program(program_archive, reports),
                Err((file_library, mut errors)) => {
                    reports.append(&mut errors);
                    let template_library = TemplateLibrary::new(definitions, file_library);
                    ParseResult::Library(template_library, reports)
                }
            }
        }
        [] => {
            reports.push(errors::NoMainError::produce_report());
            let template_library = TemplateLibrary::new(definitions, file_library);
            ParseResult::Library(template_library, reports)
        }
        _ => {
            reports.push(errors::MultipleMainError::produce_report());
            let template_library = TemplateLibrary::new(definitions, file_library);
            ParseResult::Library(template_library, reports)
        }
    }
}

fn open_file(file_path: &PathBuf) -> Result<(String, String), Report> /* path, src*/ {
    use errors::FileOsError;
    use std::fs::read_to_string;
    let path_str = format!("{}", file_path.display());
    read_to_string(file_path)
        .map(|contents| (path_str.clone(), contents))
        .map_err(|_| FileOsError {
            path: path_str.clone(),
        })
        .map_err(|error| FileOsError::produce_report(error))
}

fn parse_version_string(version: &str) -> Version {
    let split_version: Vec<&str> = version.split(".").collect();
    // This is only called on the internally defined version, so it is ok to
    // call `unwrap` here.
    (
        usize::from_str(split_version[0]).unwrap(),
        usize::from_str(split_version[1]).unwrap(),
        usize::from_str(split_version[2]).unwrap(),
    )
}

fn check_compiler_version(
    file_path: &PathBuf,
    file_version: Option<Version>,
    compiler_version: &Version,
) -> Result<ReportCollection, Report> {
    use errors::{CompilerVersionError, NoCompilerVersionWarning};
    if let Some(required_version) = file_version {
        if required_version.0 == compiler_version.0
            && required_version.1 == compiler_version.1
            && required_version.2 <= compiler_version.2
        {
            Ok(vec![])
        } else {
            let report = CompilerVersionError::produce_report(CompilerVersionError {
                path: format!("{}", file_path.display()),
                required_version: required_version,
                version: compiler_version.clone(),
            });
            Err(report)
        }
    } else {
        let report = NoCompilerVersionWarning::produce_report(NoCompilerVersionWarning {
            path: format!("{}", file_path.display()),
            version: compiler_version.clone(),
        });
        Ok(vec![report])
    }
}

/// Parse a single (function or template) definition for testing purposes.
use program_structure::ast::Definition;

pub fn parse_definition(src: &str) -> Option<Definition> {
    match parser_logic::parse_string(src) {
        Some(AST {
            mut definitions, ..
        }) if definitions.len() == 1 => definitions.pop(),
        _ => None,
    }
}
