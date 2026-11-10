use std::collections::{BTreeMap, BTreeSet};

use program_structure::file_definition::FileID;
use program_structure::report::{MessageCategory, Report, ReportLabel};

use crate::interprocedural::ContextEvidence;
use crate::application::{AnalysisObserver, ApplicationError};
use crate::rules::{RenderError, SourceMap};

/// Identical source findings share a report while retaining each affected call path.
#[derive(Default)]
pub(super) struct ReportGroups {
    groups: BTreeMap<ReportIdentity, ReportGroup>,
}

struct ReportGroup {
    first_seen: usize,
    report: Report,
    contexts: BTreeSet<ContextEvidence>,
    publication: Publication,
}

enum Publication {
    Pending,
    Published { contexts: usize },
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
struct ReportIdentity {
    id: String,
    name: String,
    category: MessageCategory,
    message: String,
    primary: Vec<LabelIdentity>,
    secondary: Vec<LabelIdentity>,
    notes: Vec<String>,
}

impl From<&Report> for ReportIdentity {
    fn from(report: &Report) -> Self {
        Self {
            id: report.id(),
            name: report.name(),
            category: *report.category(),
            message: report.message().clone(),
            primary: report.primary().iter().map(LabelIdentity::from).collect(),
            secondary: report.secondary().iter().map(LabelIdentity::from).collect(),
            notes: report.notes().clone(),
        }
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
struct LabelIdentity {
    location: ReportLocation,
    message: String,
}

impl From<&ReportLabel> for LabelIdentity {
    fn from(label: &ReportLabel) -> Self {
        Self {
            location: ReportLocation {
                file: label.file_id,
                start: label.range.start,
                end: label.range.end,
            },
            message: label.message.clone(),
        }
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
struct ReportLocation {
    file: FileID,
    start: usize,
    end: usize,
}

impl ReportGroups {
    pub(super) fn insert(&mut self, report: Report, evidence: &ContextEvidence) {
        self.group(report).contexts.insert(evidence.clone());
    }

    pub(super) fn insert_source(&mut self, report: Report) {
        self.group(report);
    }

    fn group(&mut self, report: Report) -> &mut ReportGroup {
        let first_seen = self.groups.len();
        self.groups.entry(ReportIdentity::from(&report)).or_insert_with(|| ReportGroup {
            first_seen,
            report,
            contexts: BTreeSet::new(),
            publication: Publication::Pending,
        })
    }

    pub(super) fn emit_new(
        &mut self,
        sources: &SourceMap<'_>,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<(), ApplicationError> {
        let mut groups: Vec<_> = self.groups.values_mut().collect();
        groups.sort_by_key(|group| group.first_seen);
        for group in groups {
            if let Publication::Pending = group.publication {
                group.publish(sources, observer)?;
            }
        }
        Ok(())
    }

    pub(super) fn finish(
        self,
        sources: &SourceMap<'_>,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<Vec<Report>, ApplicationError> {
        let mut groups: Vec<_> = self.groups.into_values().collect();
        groups.sort_by_key(|group| group.first_seen);
        let mut reports = Vec::with_capacity(groups.len());
        for mut group in groups {
            reports.push(group.publish(sources, observer)?);
        }
        Ok(reports)
    }
}

impl ReportGroup {
    fn publish(
        &mut self,
        sources: &SourceMap<'_>,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<Report, ApplicationError> {
        let report = self.render(sources)?;
        match self.publication {
            Publication::Pending => observer.report(&report, sources.files())?,
            Publication::Published { contexts } => {
                let paths = &report.secondary()[self.report.secondary().len()..];
                if self.contexts.len() > contexts && !paths.is_empty() {
                    observer.additional_call_paths(&report, paths, sources.files())?;
                }
            }
        }
        self.publication = Publication::Published { contexts: self.contexts.len() };
        Ok(report)
    }

    fn render(&self, sources: &SourceMap<'_>) -> Result<Report, RenderError> {
        let mut report = self.report.clone();
        if self.contexts.len() > 1 {
            add_grouped_paths(&mut report, &self.contexts, sources)?;
        } else if let Some(context) = self.contexts.first() {
            for site in context.call_path() {
                let (file, range) = sources.location(site.span())?;
                report.add_secondary(range, file, Some("Reached through this call.".into()));
            }
        }
        Ok(report)
    }
}

fn add_grouped_paths(
    report: &mut Report,
    contexts: &BTreeSet<ContextEvidence>,
    sources: &SourceMap<'_>,
) -> Result<(), RenderError> {
    let mut calls: BTreeMap<ReportLocation, Vec<String>> = BTreeMap::new();
    for (context, evidence) in contexts.iter().enumerate() {
        for (step, site) in evidence.call_path().iter().enumerate() {
            let (file, range) = sources.location(site.span())?;
            let location = ReportLocation { file, start: range.start, end: range.end };
            calls.entry(location).or_default().push(format!(
                "context {} (call {})",
                context + 1,
                step + 1,
            ));
        }
    }
    for (location, references) in calls {
        let message = format!("Observed in analyzed {}.", references.join(", "));
        report.add_secondary(location.start..location.end, location.file, Some(message));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
