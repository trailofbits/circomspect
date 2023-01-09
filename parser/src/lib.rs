extern crate num_bigint_dig as num_bigint;
extern crate num_traits;
extern crate serde;
extern crate serde_derive;
#[macro_use]
extern crate lalrpop_util;

// Silence clippy warnings for generated code.
lalrpop_mod!(#[allow(clippy::all)] pub lang);

use log::debug;

mod errors;
mod include_logic;
mod parser_logic;
use include_logic::FileStack;
use program_structure::ast::{Version, AST};
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::program_archive::ProgramArchive;
use program_structure::template_library::TemplateLibrary;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// A result from the Circom parser.
pub enum ParseResult {
    /// The program was successfully parsed without issues.
    Program(Box<ProgramArchive>, ReportCollection),
    /// The parser failed to parse a complete program.
    Library(Box<TemplateLibrary>, ReportCollection),
}

pub fn parse_files(file_paths: &[PathBuf], compiler_version: &Version) -> ParseResult {
    let mut reports = ReportCollection::new();
    let mut file_stack = FileStack::new(file_paths, &mut reports);
    let mut file_library = FileLibrary::new();
    let mut definitions = HashMap::new();
    let mut main_components = Vec::new();
    while let Some(file_path) = FileStack::take_next(&mut file_stack) {
        match parse_file(&file_path, &mut file_stack, &mut file_library, compiler_version) {
            Ok((file_id, program, mut warnings)) => {
                if let Some(main_component) = program.main_component {
                    main_components.push((file_id, main_component, program.custom_gates));
                }
                definitions.insert(file_id, program.definitions);
                reports.append(&mut warnings);
            }
            Err(error) => {
                reports.push(*error);
            }
        }
    }
    match &main_components[..] {
        [(main_id, main_component, custom_gates)] => {
            // TODO: This calls FillMeta::fill a second time.
            match ProgramArchive::new(
                file_library,
                *main_id,
                main_component,
                &definitions,
                *custom_gates,
            ) {
                Ok(program_archive) => ParseResult::Program(Box::new(program_archive), reports),
                Err((file_library, mut errors)) => {
                    reports.append(&mut errors);
                    let template_library = TemplateLibrary::new(definitions, file_library);
                    ParseResult::Library(Box::new(template_library), reports)
                }
            }
        }
        [] => {
            // TODO: Maybe use a flag to ensure that a main component must be present.
            let template_library = TemplateLibrary::new(definitions, file_library);
            ParseResult::Library(Box::new(template_library), reports)
        }
        _ => {
            reports.push(errors::MultipleMainError::produce_report());
            let template_library = TemplateLibrary::new(definitions, file_library);
            ParseResult::Library(Box::new(template_library), reports)
        }
    }
}

fn parse_file(
    file_path: &PathBuf,
    file_stack: &mut FileStack,
    file_library: &mut FileLibrary,
    compiler_version: &Version,
) -> Result<(FileID, AST, ReportCollection), Box<Report>> {
    let mut reports = ReportCollection::new();

    debug!("reading file `{}`", file_path.display());
    let (path_str, file_content) = open_file(file_path)?;
    let file_id = file_library.add_file(path_str, file_content.clone());

    debug!("parsing file `{}`", file_path.display());
    let program = parser_logic::parse_file(&file_content, file_id)?;
    for include in &program.includes {
        if let Err(report) = FileStack::add_include(file_stack, include) {
            reports.push(*report);
        }
    }
    match check_compiler_version(file_path, program.compiler_version, compiler_version) {
        Ok(warnings) => reports.extend(warnings),
        Err(error) => reports.push(*error),
    }
    Ok((file_id, program, reports))
}

fn open_file(file_path: &PathBuf) -> Result<(String, String), Box<Report>> /* path, src*/ {
    use errors::FileOsError;
    use std::fs::read_to_string;
    let path_str = format!("{}", file_path.display());
    read_to_string(file_path)
        .map(|contents| (path_str.clone(), contents))
        .map_err(|_| FileOsError { path: path_str.clone() })
        .map_err(|error| Box::new(error.into_report()))
}

fn check_compiler_version(
    file_path: &Path,
    required_version: Option<Version>,
    compiler_version: &Version,
) -> Result<ReportCollection, Box<Report>> {
    use errors::{CompilerVersionError, NoCompilerVersionWarning};
    if let Some(required_version) = required_version {
        if (required_version.0 == compiler_version.0 && required_version.1 < compiler_version.1)
            || (required_version.0 == compiler_version.0
                && required_version.1 == compiler_version.1
                && required_version.2 <= compiler_version.2)
        {
            Ok(vec![])
        } else {
            let error = CompilerVersionError {
                path: format!("{}", file_path.display()),
                required_version,
                version: *compiler_version,
            };
            Err(Box::new(error.into_report()))
        }
    } else {
        let report = NoCompilerVersionWarning::produce_report(NoCompilerVersionWarning {
            path: format!("{}", file_path.display()),
            version: *compiler_version,
        });
        Ok(vec![report])
    }
}

/// Parse a single (function or template) definition for testing purposes.
use program_structure::ast::Definition;

pub fn parse_definition(src: &str) -> Option<Definition> {
    match parser_logic::parse_string(src) {
        Some(AST { mut definitions, .. }) if definitions.len() == 1 => definitions.pop(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use crate::check_compiler_version;

    #[test]
    fn test_compiler_version() {
        let path = PathBuf::from("example.circom");

        assert!(check_compiler_version(&path, None, &(2, 1, 2)).is_ok());
        assert!(check_compiler_version(&path, Some((2, 0, 0)), &(2, 1, 2)).is_ok());
        assert!(check_compiler_version(&path, Some((2, 0, 8)), &(2, 1, 2)).is_ok());
        assert!(check_compiler_version(&path, Some((2, 1, 2)), &(2, 1, 2)).is_ok());

        // We don't support Circom 1.
        assert!(check_compiler_version(&path, Some((1, 0, 0)), &(2, 0, 8)).is_err());
        assert!(check_compiler_version(&path, Some((2, 1, 2)), &(2, 0, 8)).is_err());
        assert!(check_compiler_version(&path, Some((2, 1, 4)), &(2, 1, 2)).is_err());
    }
}
