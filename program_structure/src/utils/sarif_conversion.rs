use codespan_reporting::files::Files;
use log::{debug, trace};
use serde_sarif::sarif;
use std::fmt;
use std::ops::Range;
use std::path::PathBuf;
use thiserror::Error;

use crate::report::{Report, ReportCollection, ReportLabel};
use crate::file_definition::{FileID, FileLibrary};

// This is the Sarif file format version, not the tool version.
const SARIF_VERSION: &str = "2.1.0";
const DRIVER_NAME: &str = "Circomspect";
const ORGANIZATION: &str = "Trail of Bits";

/// A trait for objects that can be converted into a Sarif artifact.
pub trait ToSarif {
    type Sarif;
    type Error;

    /// Converts the object to the corresponding Sarif artifact.
    fn to_sarif(&self, files: &FileLibrary) -> Result<Self::Sarif, Self::Error>;
}

impl ToSarif for ReportCollection {
    type Sarif = sarif::Sarif;
    type Error = SarifError;

    fn to_sarif(&self, files: &FileLibrary) -> Result<Self::Sarif, Self::Error> {
        debug!("converting report collection to sarif-format");
        // Build reporting descriptors.
        let rules = self
            .iter()
            .map(|report| {
                sarif::ReportingDescriptorBuilder::default()
                    .name(report.name())
                    .id(report.id())
                    .build()
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(SarifError::from)?;
        // Build tool.
        trace!("building tool");
        // TODO: Should include version.
        let driver = sarif::ToolComponentBuilder::default()
            .name(DRIVER_NAME)
            .organization(ORGANIZATION)
            .rules(rules)
            .build()?;
        let tool = sarif::ToolBuilder::default().driver(driver).build()?;
        // Build run.
        trace!("building run");
        let results =
            self.iter().map(|report| report.to_sarif(files)).collect::<SarifResult<Vec<_>>>()?;
        let run = sarif::RunBuilder::default().tool(tool).results(results).build()?;
        // Build main object.
        trace!("building main sarif object");
        let sarif = sarif::SarifBuilder::default().runs(vec![run]).version(SARIF_VERSION).build();
        sarif.map_err(SarifError::from)
    }
}

impl ToSarif for Report {
    type Sarif = sarif::Result;
    type Error = SarifError;

    fn to_sarif(&self, files: &FileLibrary) -> SarifResult<sarif::Result> {
        let level = self.category().to_string();
        let rule_id = self.id();
        // Build message.
        trace!("building message");
        let message = sarif::MessageBuilder::default().text(self.message()).build()?;
        // Build locations from first primary label (or first secondary label if
        // there are no primary labels).
        //
        // Note: We currently only use the first available label to generate the
        // output. The reason for this is that the VS Code Sarif viewer does not
        // handle reports with multiple locations well.
        trace!("building locations");
        let primary_locations = self
            .primary()
            .iter()
            .map(|label| label.to_sarif(files))
            .collect::<SarifResult<Vec<_>>>()?;
        let secondary_locations = self
            .secondary()
            .iter()
            .map(|label| label.to_sarif(files))
            .collect::<SarifResult<Vec<_>>>()?;
        let locations = primary_locations
            .into_iter()
            .chain(secondary_locations.into_iter())
            .take(1)
            .collect::<Vec<_>>();
        // Build reporting descriptor reference.
        let rule = sarif::ReportingDescriptorReferenceBuilder::default()
            .id(&rule_id)
            .build()
            .map_err(SarifError::from)?;
        // Build result.
        trace!("building result");
        sarif::ResultBuilder::default()
            .level(level)
            .message(message)
            .rule_id(rule_id)
            .rule(rule)
            .locations(locations)
            .build()
            .map_err(SarifError::from)
    }
}

impl ToSarif for ReportLabel {
    type Sarif = sarif::Location;
    type Error = SarifError;

    fn to_sarif(&self, files: &FileLibrary) -> SarifResult<sarif::Location> {
        // Build artifact location.
        trace!("building artifact location");
        let file_uri = self.file_id.to_uri(files)?;
        let artifact_location = sarif::ArtifactLocationBuilder::default().uri(file_uri).build()?;
        // Build region.
        trace!("building region");
        assert!(self.range.start <= self.range.end);
        let start = files
            .to_storage()
            .location(self.file_id, self.range.start)
            .ok_or_else(|| SarifError::UnknownLocation(self.file_id, self.range.clone()))?;
        let end = files
            .to_storage()
            .location(self.file_id, self.range.end)
            .ok_or_else(|| SarifError::UnknownLocation(self.file_id, self.range.clone()))?;
        let region = sarif::RegionBuilder::default()
            .start_line(start.line_number as i64)
            .start_column(start.column_number as i64)
            .end_line(end.line_number as i64)
            .end_column(end.column_number as i64)
            .build()?;
        // Build physical location.
        trace!("building physical location");
        let physical_location = sarif::PhysicalLocationBuilder::default()
            .artifact_location(artifact_location)
            .region(region)
            .build()?;
        // Build message.
        trace!("building message");
        let message = sarif::MessageBuilder::default().text(self.message.clone()).build()?;
        // Build location.
        trace!("building location");
        sarif::LocationBuilder::default()
            .physical_location(physical_location)
            .id(0)
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
            .ok_or(SarifError::UnknownFile(*self))?
            .name()
            .replace('"', "")
            .into();
        // This path already comes from an UTF-8 string so it is ok to unwrap here.
        Ok(format!("file://{}", path.to_str().unwrap()))
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
    InvalidFix(#[from] sarif::FixBuilderError),
    UnknownLocation(FileID, Range<usize>),
    UnknownFile(FileID),
}

type SarifResult<T> = Result<T, SarifError>;

impl fmt::Display for SarifError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "failed to convert analysis results to sarif-format")
    }
}
