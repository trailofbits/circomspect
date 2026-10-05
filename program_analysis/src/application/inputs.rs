use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use program_structure::report::Report;
use program_structure::report_code::ReportCode;

/// Expand directory inputs in sorted order without following a directory cycle.
pub(super) fn expand(paths: &[PathBuf]) -> (Vec<PathBuf>, Vec<Report>) {
    let mut pending: Vec<_> = paths.iter().rev().cloned().collect();
    let mut directories = BTreeSet::new();
    let mut files = Vec::new();
    let mut reports = Vec::new();
    while let Some(path) = pending.pop() {
        if !path.is_dir() {
            if path.extension().is_some_and(|extension| extension == "circom") || !path.exists() {
                files.push(path);
            }
            continue;
        }
        let canonical = match path.canonicalize() {
            Ok(canonical) => canonical,
            Err(error) => {
                reports.push(read_error(&path, &error));
                continue;
            }
        };
        if !directories.insert(canonical) {
            continue;
        }
        match directory_files(&path) {
            Ok(mut entries) => {
                entries.sort();
                pending.extend(entries.into_iter().rev());
            }
            Err(error) => reports.push(read_error(&path, &error)),
        }
    }
    (files, reports)
}

fn directory_files(path: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    for entry in fs::read_dir(path)? {
        files.push(entry?.path());
    }
    Ok(files)
}

fn read_error(path: &Path, error: &std::io::Error) -> Report {
    Report::error(
        format!("Cannot read input directory {}: {error}", path.display()),
        ReportCode::ParseFail,
    )
}
