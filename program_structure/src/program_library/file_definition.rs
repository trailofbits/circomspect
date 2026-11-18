use codespan_reporting::files::SimpleFiles;
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
    #[must_use]
    pub fn new() -> FileLibrary {
        FileLibrary::default()
    }
    pub fn add_file(
        &mut self,
        file_name: FilePath,
        file_source: FileSource,
        is_user_input: bool,
    ) -> FileID {
        let file_id = self.files.add(file_name, file_source);
        if is_user_input {
            self.user_inputs.insert(file_id);
        }
        file_id
    }

    #[must_use]
    pub fn to_storage(&self) -> &FileStorage {
        &self.files
    }

    #[must_use]
    pub fn user_inputs(&self) -> &HashSet<FileID> {
        &self.user_inputs
    }
}
