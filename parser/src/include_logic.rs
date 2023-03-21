use crate::errors::FileOsError;

use super::errors::IncludeError;
use program_structure::ast::Include;
use program_structure::report::{Report, ReportCollection};
use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;

pub struct FileStack {
    current_location: Option<PathBuf>,
    black_paths: HashSet<PathBuf>,
    user_inputs: HashSet<PathBuf>,
    stack: Vec<PathBuf>,
}

impl FileStack {
    pub fn new(paths: &[PathBuf], reports: &mut ReportCollection) -> FileStack {
        let mut result = FileStack {
            current_location: None,
            black_paths: HashSet::new(),
            user_inputs: HashSet::new(),
            stack: Vec::new(),
        };
        result.add_files(paths, reports);
        result.user_inputs = result.stack.iter().cloned().collect::<HashSet<_>>();

        result
    }

    fn add_files(&mut self, paths: &[PathBuf], reports: &mut ReportCollection) {
        for path in paths {
            if path.is_dir() {
                // Handle directories on a best effort basis only.
                let mut paths = Vec::new();
                if let Ok(entries) = fs::read_dir(path) {
                    for entry in entries.flatten() {
                        paths.push(entry.path())
                    }
                }
                self.add_files(&paths, reports);
            } else if let Some(extension) = path.extension() {
                // Add Circom files to file stack.
                if extension == "circom" {
                    match fs::canonicalize(path) {
                        Ok(path) => self.stack.push(path),
                        Err(_) => {
                            reports.push(
                                FileOsError { path: path.display().to_string() }.into_report(),
                            );
                        }
                    }
                }
            }
        }
    }

    pub fn add_include(&mut self, include: &Include) -> Result<(), Box<Report>> {
        let mut location = self.current_location.clone().expect("parsing file");
        location.push(include.path.clone());
        match fs::canonicalize(location) {
            Ok(path) => {
                if !self.black_paths.contains(&path) {
                    self.stack.push(path);
                }
                Ok(())
            }
            Err(_) => {
                let error = IncludeError {
                    path: include.path.clone(),
                    file_id: include.meta.file_id,
                    file_location: include.meta.file_location(),
                };
                Err(Box::new(error.into_report()))
            }
        }
    }

    pub fn take_next(&mut self) -> Option<PathBuf> {
        loop {
            match self.stack.pop() {
                None => {
                    break None;
                }
                Some(file_path) if !self.black_paths.contains(&file_path) => {
                    let mut location = file_path.clone();
                    location.pop();
                    self.current_location = Some(location);
                    self.black_paths.insert(file_path.clone());
                    break Some(file_path);
                }
                _ => {}
            }
        }
    }

    pub fn is_user_input(&self, path: &PathBuf) -> bool {
        self.user_inputs.contains(path)
    }
}
