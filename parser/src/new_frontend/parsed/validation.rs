use crate::new_frontend::ast::{DiagnosticKind, SyntaxDiagnostic, Version, VersionPolicy};
use crate::new_frontend::parsed::{Annotation, Parsed, ParsedItem, ParsedSegment};
use crate::new_frontend::parsed::{Recovery, SourceForm};
use crate::new_frontend::typed::{Item, PendingFeatureCheck, PendingFeatureKind};

fn minimum_version(annotation: &Annotation) -> Option<Version> {
    match annotation.form {
        SourceForm::CustomTemplates => Some(Version::new(2, 0, 6)),
        SourceForm::Feature(version) => Some(version),
        SourceForm::Array if annotation.facts.anonymous_call => Some(Version::new(2, 2, 3)),
        SourceForm::AnonymousCall | SourceForm::Array | SourceForm::Tuple => {
            Some(Version::new(2, 1, 0))
        }
        SourceForm::Plain | SourceForm::PotentialBus | SourceForm::Recovery(_) => None,
    }
}

fn validate_feature(
    annotation: &Annotation,
    target: Version,
    declared: Option<Version>,
    diagnostics: &mut Vec<SyntaxDiagnostic>,
) {
    let Some(minimum) = minimum_version(annotation) else { return };
    let declared_too_old = if let SourceForm::CustomTemplates = annotation.form {
        declared.is_some_and(|version| version < minimum)
    } else {
        false
    };
    if target < minimum || declared_too_old {
        diagnostics.push(SyntaxDiagnostic::new(
            DiagnosticKind::FeatureVersion,
            annotation.span,
            format!(
                "feature requires Circom {}.{}.{}",
                minimum.major, minimum.minor, minimum.patch
            ),
        ));
    }
}

fn validate_versions(
    segments: &[ParsedSegment],
    policy: VersionPolicy,
    diagnostics: &mut Vec<SyntaxDiagnostic>,
) -> Vec<PendingFeatureCheck> {
    let declared = segments.iter().find_map(|segment| segment.item.declared_version());
    for segment in segments {
        if let ParsedItem::InvalidVersion { diagnostic, .. } = &segment.item {
            diagnostics.push(diagnostic.clone());
        }
    }
    if let Some(version) = declared {
        if version.major != policy.supported.major || version > policy.supported {
            if let Some(segment) =
                segments.iter().find(|segment| segment.item.declared_version().is_some())
            {
                diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::UnsupportedVersion,
                    segment.span(),
                    format!(
                        "source requires Circom {}.{}.{}, but the supported target is {}.{}.{}",
                        version.major,
                        version.minor,
                        version.patch,
                        policy.supported.major,
                        policy.supported.minor,
                        policy.supported.patch
                    ),
                ));
            }
        }
    }
    let mut pending = Vec::new();
    for segment in segments {
        segment.visit(|annotation| {
            validate_feature(annotation, policy.supported, declared, diagnostics);
            collect_pending(segment, annotation, policy.supported, &mut pending);
        });
    }
    pending
}

fn collect_pending(
    segment: &ParsedSegment,
    annotation: &Annotation,
    target: Version,
    pending: &mut Vec<PendingFeatureCheck>,
) {
    let SourceForm::Array = annotation.form else { return };
    if target >= Version::new(2, 2, 3) || annotation.facts.anonymous_call {
        return;
    }
    let potential_bus =
        annotation.children.iter().any(|id| segment.context.annotations[id.0].facts.potential_bus);
    if potential_bus {
        pending.push(PendingFeatureCheck {
            kind: PendingFeatureKind::InlineArrayElementType,
            span: annotation.span,
            required_version: Version::new(2, 2, 3),
        });
    }
}

fn item_stage(item: &ParsedItem) -> Option<u8> {
    match item {
        ParsedItem::InvalidVersion { .. }
        | ParsedItem::Ready(Parsed { value: Item::Pragma { .. }, .. }) => Some(0),
        ParsedItem::Ready(Parsed { value: Item::Include { .. }, .. }) => Some(1),
        ParsedItem::Ready(Parsed { value: Item::Definition(_), .. }) => Some(2),
        ParsedItem::Ready(Parsed { value: Item::Main { .. }, .. }) => Some(3),
        ParsedItem::Ready(Parsed { value: Item::Error { .. }, .. }) => None,
    }
}

fn validate_order(segments: &[ParsedSegment], diagnostics: &mut Vec<SyntaxDiagnostic>) {
    let mut stage = 0;
    for segment in segments {
        let Some(expected) = item_stage(&segment.item) else { continue };
        if expected < stage || (expected == 3 && stage == 3) {
            diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::Syntax,
                segment.span(),
                "pragma, include, definition, and main declarations are out of order",
            ));
        }
        stage = stage.max(expected);
        segment.visit(|annotation| {
            let SourceForm::Recovery(recovery) = annotation.form else { return };
            let message = match recovery {
                Recovery::StatementBoundary => {
                    "invalid statement; parsing continued at the next statement or block boundary"
                }
                Recovery::ExpressionStatement => {
                    "only an anonymous component call may be used as an expression statement"
                }
            };
            diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::Syntax,
                annotation.span,
                message,
            ));
        });
    }
}

pub(crate) fn finish_segments(
    segments: Vec<ParsedSegment>,
    policy: VersionPolicy,
    diagnostics: &mut Vec<SyntaxDiagnostic>,
) -> (Vec<Item>, Vec<PendingFeatureCheck>) {
    let pending = validate_versions(&segments, policy, diagnostics);
    validate_order(&segments, diagnostics);
    let mut items = Vec::with_capacity(segments.len());
    for segment in segments {
        let span = segment.span();
        match segment.item {
            ParsedItem::Ready(item) => items.push(item.value),
            ParsedItem::InvalidVersion { diagnostic, .. } => {
                diagnostics.push(diagnostic);
                items.push(Item::Error { span });
            }
        }
    }
    (items, pending)
}
