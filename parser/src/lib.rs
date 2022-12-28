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
mod syntax_sugar_traits;
mod syntax_sugar_remover;

pub use parser_logic::parse_definition;

use include_logic::FileStack;
use program_structure::ast::{Version, AST};
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::program_archive::ProgramArchive;
use program_structure::template_library::TemplateLibrary;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::str::FromStr;

pub enum ParseResult {
    // The program was successfully parsed without issues.
    Program(Box<ProgramArchive>, ReportCollection),
    // The parser failed to parse a complete program.
    Library(Box<TemplateLibrary>, ReportCollection),
}

pub fn parse_files(file_paths: &Vec<PathBuf>, compiler_version: &str) -> ParseResult {
    let compiler_version = parse_version_string(compiler_version);

    let mut reports = ReportCollection::new();
    let mut file_stack = FileStack::new(file_paths, &mut reports);
    let mut file_library = FileLibrary::new();
    let mut definitions = HashMap::new();
    let mut main_components = Vec::new();
    while let Some(file_path) = FileStack::take_next(&mut file_stack) {
        match parse_file(&file_path, &mut file_stack, &mut file_library, &compiler_version) {
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
    // Create a parse result.
    let mut result = match &main_components[..] {
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
    };
    // Remove anonymous components and tuples.
    //
    // TODO: This could be moved to the lifting phase.
    match &mut result {
        ParseResult::Program(program_archive, reports) => {
            if program_archive.main_expression().is_anonymous_component() {
                reports.push(
                    errors::AnonymousComponentError::new(
                        Some(program_archive.main_expression().meta()),
                        "The main component cannot contain an anonymous call.",
                        Some("Main component defined here."),
                    )
                    .into_report(),
                );
            }
            let (new_templates, new_functions) = syntax_sugar_remover::remove_syntactic_sugar(
                &program_archive.templates,
                &program_archive.functions,
                &program_archive.file_library,
                reports,
            );
            program_archive.templates = new_templates;
            program_archive.functions = new_functions;
        }
        ParseResult::Library(template_library, reports) => {
            let (new_templates, new_functions) = syntax_sugar_remover::remove_syntactic_sugar(
                &template_library.templates,
                &template_library.functions,
                &template_library.file_library,
                reports,
            );
            template_library.templates = new_templates;
            template_library.functions = new_functions;
        }
    }
    result
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
        if let Err(report) = file_stack.add_include(include) {
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

fn parse_version_string(version: &str) -> Version {
    let split_version: Vec<&str> = version.split('.').collect();
    // This is only called on the internally defined version, so it is ok to
    // call `unwrap` here.
    (
        usize::from_str(split_version[0]).unwrap(),
        usize::from_str(split_version[1]).unwrap(),
        usize::from_str(split_version[2]).unwrap(),
    )
}

fn check_compiler_version(
    file_path: &Path,
    required_version: Option<Version>,
    compiler_version: &Version,
) -> Result<ReportCollection, Box<Report>> {
    use errors::{CompilerVersionError, NoCompilerVersionWarning};
    if let Some(required_version) = required_version {
        if required_version.0 == compiler_version.0
            && required_version.1 == compiler_version.1
            && required_version.2 <= compiler_version.2
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
