use codespan_reporting::files::{Files, SimpleFiles};
use std::{ops::Range, collections::HashSet};

pub type FileSource = String;
pub type FilePath = String;
pub type FileID = usize;
pub type FileLocation = Range<usize>;
type FileStorage = SimpleFiles<FilePath, FileSource>;

#[derive(Clone)]
pub struct FileLibrary {
    files: FileStorage,
    user_inputs: HashSet<FileID>,
}

impl Default for FileLibrary {
    fn default() -> Self {
        FileLibrary { files: FileStorage::new(), user_inputs: HashSet::new() }
    }
}

impl FileLibrary {
    pub fn new() -> FileLibrary {
        FileLibrary::default()
    }
    pub fn add_file(
        &mut self,
        file_name: FilePath,
        file_source: FileSource,
        is_user_input: bool,
    ) -> FileID {
        let file_id = self.get_mut_files().add(file_name, file_source);
        if is_user_input {
            self.user_inputs.insert(file_id);
        }
        file_id
    }

    pub fn get_line(&self, start: usize, file_id: FileID) -> Option<usize> {
        self.files.line_index(file_id, start).map(|lines| lines + 1).ok()
    }

    pub fn to_storage(&self) -> &FileStorage {
        self.get_files()
    }

    pub fn user_inputs(&self) -> &HashSet<FileID> {
        &self.user_inputs
    }

    pub fn is_user_input(&self, file_id: FileID) -> bool {
        self.user_inputs.contains(&file_id)
    }

    fn get_files(&self) -> &FileStorage {
        &self.files
    }

    fn get_mut_files(&mut self) -> &mut FileStorage {
        &mut self.files
    }
}

pub fn generate_file_location(start: usize, end: usize) -> FileLocation {
    start..end
}
