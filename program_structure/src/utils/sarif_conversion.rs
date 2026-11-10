use codespan_reporting::files::Files;
use log::{debug, trace};
use serde_sarif::sarif;
use std::collections::BTreeSet;
use std::fmt;
use std::ops::Range;
use std::path::PathBuf;
use thiserror::Error;
use url::Url;

use crate::report::{Report, ReportCollection, ReportLabel};
use crate::file_definition::{FileID, FileLibrary};

// This is the Sarif file format version, not the tool version.
const SARIF_VERSION: &str = "2.1.0";
const DRIVER_NAME: &str = "Circomspect";
const ORGANIZATION: &str = "Trail of Bits";
const DOWNLOAD_URI: &str = "https://github.com/trailofbits/circomspect";

/// A trait for objects that can be converted into a Sarif artifact.
pub trait ToSarif {
    type Sarif;
    type Error;

    /// Converts the object to the corresponding Sarif artifact.
    ///
    /// # Errors
    /// Returns an error for an unknown file, invalid source span, non-absolute
    /// source path, or invalid SARIF object.
    fn to_sarif(&self, files: &FileLibrary) -> Result<Self::Sarif, Self::Error>;
}

impl ToSarif for ReportCollection {
    type Sarif = sarif::Sarif;
    type Error = SarifError;

    fn to_sarif(&self, files: &FileLibrary) -> Result<Self::Sarif, Self::Error> {
        debug!("converting report collection to Sarif-format");
        trace!("building reporting descriptors");
        let rules = self
            .iter()
            .map(|report| (report.name(), report.id()))
            .collect::<BTreeSet<_>>()
            .iter()
            .map(|(name, id)| {
                sarif::ReportingDescriptorBuilder::default().name(name).id(id).build()
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(SarifError::from)?;
        // TODO: Should include primary package version.
        trace!("building tool");
        let driver = sarif::ToolComponentBuilder::default()
            .name(DRIVER_NAME)
            .organization(ORGANIZATION)
            .download_uri(DOWNLOAD_URI)
            .rules(rules)
            .build()?;
        let tool = sarif::ToolBuilder::default().driver(driver).build()?;
        trace!("building run");
        let results =
            self.iter().map(|report| report.to_sarif(files)).collect::<SarifResult<Vec<_>>>()?;
        let run = sarif::RunBuilder::default()
            .tool(tool)
            .results(results)
            .column_kind(serde_json::Value::String("unicodeCodePoints".into()))
            .build()?;
        trace!("building main Sarif object");
        let sarif = sarif::SarifBuilder::default().runs(vec![run]).version(SARIF_VERSION).build();
        sarif.map_err(SarifError::from)
    }
}

impl ToSarif for Report {
    type Sarif = sarif::Result;
    type Error = SarifError;

    fn to_sarif(&self, files: &FileLibrary) -> SarifResult<sarif::Result> {
        let level = self.category().to_level();
        let rule_id = self.id();
        trace!("building message");
        let mut text = self.message().clone();
        for note in self.notes() {
            text.push('\n');
            text.push_str(note);
        }
        let message = sarif::MessageBuilder::default().text(text).build()?;
        trace!("building locations");
        let mut locations = self
            .primary()
            .iter()
            .map(|label| label.to_sarif(files))
            .collect::<SarifResult<Vec<_>>>()?;
        let mut related_locations = self
            .secondary()
            .iter()
            .map(|label| label.to_sarif(files))
            .collect::<SarifResult<Vec<_>>>()?;
        for (id, location) in (0_i64..).zip(locations.iter_mut().chain(&mut related_locations)) {
            location.id = Some(id);
        }
        let rule = sarif::ReportingDescriptorReferenceBuilder::default()
            .id(&rule_id)
            .build()
            .map_err(SarifError::from)?;
        trace!("building result");
        sarif::ResultBuilder::default()
            .level(level)
            .message(message)
            .rule_id(rule_id)
            .rule(rule)
            .locations(locations)
            .related_locations(related_locations)
            .build()
            .map_err(SarifError::from)
    }
}

impl ToSarif for ReportLabel {
    type Sarif = sarif::Location;
    type Error = SarifError;

    fn to_sarif(&self, files: &FileLibrary) -> SarifResult<sarif::Location> {
        trace!("building artifact location");
        let file_uri = self.file_id.to_uri(files)?;
        let artifact_location = sarif::ArtifactLocationBuilder::default().uri(file_uri).build()?;
        trace!("building region");
        if self.range.start > self.range.end {
            return Err(SarifError::UnknownLocation(self.file_id, self.range.clone()));
        }
        let start = files
            .to_storage()
            .location(self.file_id, self.range.start)
            .map_err(|_| SarifError::UnknownLocation(self.file_id, self.range.clone()))?;
        let end = files
            .to_storage()
            .location(self.file_id, self.range.end)
            .map_err(|_| SarifError::UnknownLocation(self.file_id, self.range.clone()))?;
        let region = sarif::RegionBuilder::default()
            .start_line(
                i64::try_from(start.line_number)
                    .map_err(|_| SarifError::UnknownLocation(self.file_id, self.range.clone()))?,
            )
            .start_column(
                i64::try_from(start.column_number)
                    .map_err(|_| SarifError::UnknownLocation(self.file_id, self.range.clone()))?,
            )
            .end_line(
                i64::try_from(end.line_number)
                    .map_err(|_| SarifError::UnknownLocation(self.file_id, self.range.clone()))?,
            )
            .end_column(
                i64::try_from(end.column_number)
                    .map_err(|_| SarifError::UnknownLocation(self.file_id, self.range.clone()))?,
            )
            .build()?;
        trace!("building physical location");
        let physical_location = sarif::PhysicalLocationBuilder::default()
            .artifact_location(artifact_location)
            .region(region)
            .build()?;
        trace!("building message");
        let message = sarif::MessageBuilder::default().text(self.message.clone()).build()?;
        trace!("building location");
        sarif::LocationBuilder::default()
            .physical_location(physical_location)
            .message(message)
            .build()
            .map_err(SarifError::from)
    }
}

trait ToUri {
    type Error;
    fn to_uri(&self, files: &FileLibrary) -> Result<String, Self::Error>;
}

impl ToUri for FileID {
    type Error = SarifError;

    fn to_uri(&self, files: &FileLibrary) -> Result<String, SarifError> {
        let path: PathBuf = files
            .to_storage()
            .get(*self)
            .map_err(|_| SarifError::UnknownFile(*self))?
            .name()
            .into();
        Url::from_file_path(&path).map(String::from).map_err(|()| SarifError::InvalidFilePath(path))
    }
}

#[derive(Error, Debug)]
pub enum SarifError {
    InvalidReportingDescriptorReference(#[from] sarif::ReportingDescriptorReferenceBuilderError),
    InvalidReportingDescriptor(#[from] sarif::ReportingDescriptorBuilderError),
    InvalidPhysicalLocationError(#[from] sarif::PhysicalLocationBuilderError),
    InvalidArtifactLocation(#[from] sarif::ArtifactLocationBuilderError),
    InvalidToolComponent(#[from] sarif::ToolComponentBuilderError),
    InvalidLocation(#[from] sarif::LocationBuilderError),
    InvalidMessage(#[from] sarif::MessageBuilderError),
    InvalidRegion(#[from] sarif::RegionBuilderError),
    InvalidResult(#[from] sarif::ResultBuilderError),
    InvalidRun(#[from] sarif::RunBuilderError),
    InvalidSarif(#[from] sarif::SarifBuilderError),
    InvalidTool(#[from] sarif::ToolBuilderError),
    UnknownLocation(FileID, Range<usize>),
    UnknownFile(FileID),
    InvalidFilePath(PathBuf),
}

type SarifResult<T> = Result<T, SarifError>;

impl fmt::Display for SarifError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Self::InvalidFilePath(path) = self {
            return write!(
                f,
                "cannot encode source path {} as an absolute file URI",
                path.display()
            );
        }
        if let Self::UnknownLocation(file, range) = self {
            return write!(f, "invalid source range {range:?} in file {file}");
        }
        write!(f, "failed to convert analysis results to Sarif format")
    }
}
