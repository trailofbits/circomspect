use super::errors::FileOsError;
use program_structure::error_definition::Report;
use std::collections::HashSet;
use std::path::PathBuf;

pub struct FileStack {
    current_location: Option<PathBuf>,
    black_paths: HashSet<PathBuf>,
    stack: Vec<PathBuf>,
}

impl FileStack {
    pub fn new(file_paths: &Vec<PathBuf>) -> FileStack {
        let location = file_paths
            .iter()
            .next()
            .cloned()
            .map(|mut file_path| {
                file_path.pop();
                file_path
            });
        FileStack {
            current_location: location,
            black_paths: HashSet::new(),
            stack: file_paths.clone(),
        }
    }

    pub fn add_include(stack: &mut FileStack, path: String) -> Result<(), Report> {
        if let Some(mut location) = stack.current_location.clone() {
            location.push(path.clone());
            let path = std::fs::canonicalize(location)
                .map_err(|_| FileOsError { path: path.clone() })
                .map_err(|e| FileOsError::produce_report(e))?;
            if !stack.black_paths.contains(&path) {
                stack.stack.push(path);
            }
        }
        Ok(())
    }

    pub fn take_next(stack: &mut FileStack) -> Option<PathBuf> {
        loop {
            match stack.stack.pop() {
                None => {
                    break None;
                }
                Some(file_path) if !stack.black_paths.contains(&file_path) => {
                    let mut location = file_path.clone();
                    location.pop();
                    stack.current_location = Some(location);
                    stack.black_paths.insert(file_path.clone());
                    break Some(file_path);
                }
                _ => {}
            }
        }
    }
}
