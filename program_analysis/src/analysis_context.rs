use thiserror::Error;

use program_structure::{
    file_definition::{FileID, FileLocation},
    cfg::Cfg,
};

/// Errors returned by the analysis context.
#[derive(Debug, Error)]
pub enum AnalysisError {
    /// This function has no corresponding AST.
    #[error("Unknown function `{name}`.")]
    UnknownFunction { name: String },
    /// This template has no corresponding AST.
    #[error("Unknown template `{name}`.")]
    UnknownTemplate { name: String },
    /// This function has an AST, but we failed to lift it to a corresponding
    /// CFG.
    #[error("Failed to lift the function `{name}`.")]
    FailedToLiftFunction { name: String },
    /// This template has an AST, but we failed to lift it to a corresponding
    /// CFG.
    #[error("Failed to lift the template `{name}`.")]
    FailedToLiftTemplate { name: String },
    /// The file ID does not correspond to a known file.
    #[error("Unknown file ID `{file_id}`.")]
    UnknownFile { file_id: FileID },
    /// The location does not exist in the file with the given ID.
    #[error("The location `{}:{}` is not valid for the file with file ID `{file_id}`.", file_location.start, file_location.end)]
    InvalidLocation { file_id: FileID, file_location: FileLocation },
}

/// Context passed to each analysis pass.
pub trait AnalysisContext {
    type Error;

    /// Returns true if the context knows of a function with the given name.
    /// This method does not compute the CFG of the function which saves time
    /// compared to `AnalysisContext::function`.
    fn is_function(&self, name: &str) -> bool;

    /// Returns true if the context knows of a template with the given name.
    /// This method does not compute the CFG of the template which saves time
    /// compared to `AnalysisContext::template`.
    fn is_template(&self, name: &str) -> bool;

    /// Returns the CFG for the function with the given name.
    fn function(&mut self, name: &str) -> Result<&Cfg, Self::Error>;

    /// Returns the CFG for the template with the given name.
    fn template(&mut self, name: &str) -> Result<&Cfg, Self::Error>;

    /// Returns the string corresponding to the given file ID and location.
    fn underlying_str(
        &self,
        file_id: &FileID,
        file_location: &FileLocation,
    ) -> Result<String, Self::Error>;
}
