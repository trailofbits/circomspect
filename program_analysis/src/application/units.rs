use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::Arc;

use parser::frontend::{load_sources, Item, LoadedProject, SourceId, Version, VersionPolicy};
use program_structure::file_definition::{FileID, FileLibrary};

use crate::application::ApplicationError;

pub(super) struct Unit {
    pub loaded: LoadedProject,
    root: Option<PathBuf>,
}

impl Unit {
    pub fn roots(&self) -> Vec<SourceId> {
        self.loaded
            .files
            .iter()
            .filter(|file| self.root.as_ref() == Some(&file.path))
            .map(|file| file.id)
            .collect()
    }

    pub fn open_namespace(&self) -> bool {
        !self
            .loaded
            .files
            .iter()
            .any(|file| file.outcome.ast.items.iter().any(|item| matches!(item, Item::Main { .. })))
    }
}

pub(super) fn distinct_paths(paths: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut seen = BTreeSet::new();
    paths
        .into_iter()
        .filter(|path| seen.insert(path.canonicalize().unwrap_or_else(|_| path.clone())))
        .collect()
}

pub(super) fn load(path: Option<&PathBuf>, libraries: &[PathBuf]) -> Unit {
    if let Some(path) = path {
        let root = path.canonicalize().ok();
        let loaded = load_sources(
            std::slice::from_ref(path),
            libraries,
            VersionPolicy::new(Version::new(2, 2, 3)),
        );
        Unit { loaded, root }
    } else {
        let loaded = load_sources(&[], libraries, VersionPolicy::new(Version::new(2, 2, 3)));
        Unit { loaded, root: None }
    }
}

pub(super) fn catalog(
    paths: &[PathBuf],
    libraries: &[PathBuf],
) -> Result<(Arc<FileLibrary>, BTreeMap<PathBuf, FileID>), ApplicationError> {
    let roots: BTreeSet<_> = paths.iter().filter_map(|path| path.canonicalize().ok()).collect();
    let mut files = FileLibrary::new();
    let mut file_ids = BTreeMap::new();
    for path in paths {
        let unit = load(Some(path), libraries);
        for source in &unit.loaded.files {
            if let Some(file_id) = file_ids.get(&source.path) {
                let previous = files.to_storage().get(*file_id).map_err(|error| {
                    ApplicationError::Invariant(format!(
                        "catalog cannot read {}: {error}",
                        source.path.display()
                    ))
                })?;
                if previous.source() != &source.text {
                    return Err(ApplicationError::Invariant(format!(
                        "source changed while loading {}",
                        source.path.display()
                    )));
                }
                continue;
            }
            let file_id = files.add_file(
                source.path.to_string_lossy().into_owned(),
                source.text.clone(),
                roots.contains(&source.path),
            );
            file_ids.insert(source.path.clone(), file_id);
        }
    }
    Ok((Arc::new(files), file_ids))
}
