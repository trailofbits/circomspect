//! Typed grammar values and source-only validation metadata for one parsed segment.

mod construct;
mod expressions;
mod headers;
mod validation;

use crate::new_frontend::ast::{SourceId, Span, SyntaxDiagnostic, Version};
use crate::new_frontend::typed::{Item, Pragma};

pub(super) use construct::{DeclarationParts, DefinitionParts, ForParts, TemplateModifier};
pub(super) use expressions::AnonymousParts;
pub(super) use headers::{BusHeaderParts, HeaderDirection};
pub(super) use validation::finish_segments;

#[derive(Clone, Copy)]
pub(super) struct AnnotationId(usize);

pub(super) struct Parsed<T> {
    pub value: T,
    pub annotation: AnnotationId,
}

impl<T> Parsed<T> {
    pub fn map<U>(self, map: impl FnOnce(T) -> U) -> Parsed<U> {
        Parsed { value: map(self.value), annotation: self.annotation }
    }
}

#[derive(Clone, Copy, Default)]
struct SourceFacts {
    anonymous_call: bool,
    potential_bus: bool,
}

#[derive(Clone, Copy)]
pub(super) enum Recovery {
    StatementBoundary,
    ExpressionStatement,
}

#[derive(Clone, Copy)]
pub(super) enum SourceForm {
    Plain,
    PotentialBus,
    AnonymousCall,
    Array,
    Tuple,
    Feature(Version),
    CustomTemplates,
    Recovery(Recovery),
}

struct Annotation {
    span: Span,
    form: SourceForm,
    children: Vec<AnnotationId>,
    facts: SourceFacts,
}

pub(super) enum ParsedItem {
    Ready(Parsed<Item>),
    InvalidVersion { annotation: AnnotationId, diagnostic: SyntaxDiagnostic },
}

impl ParsedItem {
    fn annotation(&self) -> AnnotationId {
        match self {
            Self::Ready(item) => item.annotation,
            Self::InvalidVersion { annotation, diagnostic: _ } => *annotation,
        }
    }

    fn declared_version(&self) -> Option<Version> {
        let Self::Ready(Parsed {
            value: Item::Pragma { pragma: Pragma::Version(version), .. },
            ..
        }) = self
        else {
            return None;
        };
        Some(*version)
    }
}

pub(super) struct ParsedSegment {
    context: ParseContext,
    item: ParsedItem,
}

impl ParsedSegment {
    pub fn error(source: SourceId, span: Span) -> Self {
        let mut context = ParseContext::new(source);
        let item = context.plain(Item::Error { span }, span, Vec::new());
        context.finish(ParsedItem::Ready(item))
    }

    fn span(&self) -> Span {
        self.context.annotations[self.item.annotation().0].span
    }

    fn visit(&self, mut visit: impl FnMut(&Annotation)) {
        let mut work = vec![self.item.annotation()];
        while let Some(id) = work.pop() {
            let annotation = &self.context.annotations[id.0];
            visit(annotation);
            for child in annotation.children.iter().rev() {
                work.push(*child);
            }
        }
    }
}

pub(super) struct ParseContext {
    source: SourceId,
    annotations: Vec<Annotation>,
}

impl ParseContext {
    pub fn new(source: SourceId) -> Self {
        Self { source, annotations: Vec::new() }
    }

    pub fn span(&self, start: usize, end: usize) -> Span {
        Span::from_lexer(self.source, start, end)
    }

    pub fn finish(self, item: ParsedItem) -> ParsedSegment {
        ParsedSegment { context: self, item }
    }

    pub fn annotate<T>(
        &mut self,
        value: T,
        span: Span,
        children: Vec<AnnotationId>,
        form: SourceForm,
    ) -> Parsed<T> {
        let mut facts = SourceFacts::default();
        for child in &children {
            let child = self.annotations[child.0].facts;
            facts.anonymous_call |= child.anonymous_call;
            facts.potential_bus |= child.potential_bus;
        }
        match form {
            SourceForm::PotentialBus | SourceForm::Array | SourceForm::Tuple => {
                facts.potential_bus = true;
            }
            SourceForm::AnonymousCall => facts.anonymous_call = true,
            SourceForm::Plain
            | SourceForm::Feature(_)
            | SourceForm::CustomTemplates
            | SourceForm::Recovery(_) => {}
        }
        let annotation = AnnotationId(self.annotations.len());
        self.annotations.push(Annotation { span, form, children, facts });
        Parsed { value, annotation }
    }

    pub fn plain<T>(&mut self, value: T, span: Span, children: Vec<AnnotationId>) -> Parsed<T> {
        self.annotate(value, span, children, SourceForm::Plain)
    }

    pub fn list<T>(&mut self, span: Span, values: Vec<Parsed<T>>) -> Parsed<Vec<T>> {
        let (values, children) = unpack(values);
        self.plain(values, span, children)
    }
}

pub(super) fn unpack<T>(items: Vec<Parsed<T>>) -> (Vec<T>, Vec<AnnotationId>) {
    let mut values = Vec::with_capacity(items.len());
    let mut children = Vec::with_capacity(items.len());
    for item in items {
        values.push(item.value);
        children.push(item.annotation);
    }
    (values, children)
}
