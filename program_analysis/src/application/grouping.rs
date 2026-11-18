use std::collections::{BTreeMap, BTreeSet};

use program_structure::file_definition::FileID;
use program_structure::report::{MessageCategory, Report, ReportLabel};

use crate::interprocedural::CallContext;

mod context;
pub(super) use context::ContextDisplay;
use crate::application::{AnalysisObserver, ApplicationError};
use crate::rules::{RenderError, SourceMap};

/// Identical source findings share one report and optional context qualifications.
#[derive(Default)]
pub(super) struct ReportGroups {
    groups: BTreeMap<ReportIdentity, ReportGroup>,
}

struct ReportGroup {
    first_seen: usize,
    report: Report,
    qualifications: BTreeMap<CallContext, (parser::frontend::Span, String)>,
    publication: Publication,
}

enum Publication {
    Pending,
    Published { contexts: BTreeSet<CallContext> },
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ReportIdentity {
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
    pub(super) fn insert(&mut self, report: Report, display: ContextDisplay) {
        let group = self.group(report);
        if let ContextDisplay::Qualify { context: key, span, message } = display {
            let replace = group.qualifications.get(&key).map_or(true, |(current, _)| {
                (span.source(), span.start(), span.end())
                    < (current.source(), current.start(), current.end())
            });
            if replace {
                group.qualifications.insert(key, (span, message));
            }
        }
    }

    pub(super) fn insert_source(&mut self, report: Report) {
        self.group(report);
    }

    fn group(&mut self, report: Report) -> &mut ReportGroup {
        let first_seen = self.groups.len();
        self.groups.entry(ReportIdentity::from(&report)).or_insert_with(|| ReportGroup {
            first_seen,
            report,
            qualifications: BTreeMap::new(),
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
        match &self.publication {
            Publication::Pending => observer.report(&report, sources.files())?,
            Publication::Published { contexts } => {
                if self.qualifications.keys().any(|context| !contexts.contains(context)) {
                    let qualifications = &report.secondary()[self.report.secondary().len()..];
                    observer.additional_call_paths(&report, qualifications, sources.files())?;
                }
            }
        }
        self.publication =
            Publication::Published { contexts: self.qualifications.keys().cloned().collect() };
        Ok(report)
    }

    fn render(&self, sources: &SourceMap<'_>) -> Result<Report, RenderError> {
        let mut report = self.report.clone();
        for (span, message) in self.qualifications.values() {
            let (file, range) = sources.location(*span)?;
            report.add_secondary(range, file, Some(message.clone()));
        }
        Ok(report)
    }
}

#[cfg(test)]
mod tests;
