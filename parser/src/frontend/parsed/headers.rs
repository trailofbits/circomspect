use crate::frontend::source::{Span, Version};
use crate::frontend::parsed::construct::arguments;
use crate::frontend::parsed::{AnnotationId, ParseContext, Parsed, SourceForm};
use crate::frontend::ast::{DeclarationKind, DirectionSyntax, Expression, Identifier, SpannedDirection};

pub(crate) enum HeaderDirection {
    Before(Parsed<SpannedDirection>),
    After(Option<Parsed<SpannedDirection>>),
}

impl HeaderDirection {
    fn into_parts(self) -> (DirectionSyntax, Option<AnnotationId>) {
        match self {
            Self::Before(direction) => {
                (DirectionSyntax::Before(direction.value), Some(direction.annotation))
            }
            Self::After(Some(direction)) => {
                (DirectionSyntax::After(direction.value), Some(direction.annotation))
            }
            Self::After(None) => (DirectionSyntax::Unspecified, None),
        }
    }
}

pub(crate) struct BusHeaderParts {
    pub name: Parsed<Identifier>,
    pub arguments: Option<Parsed<Vec<Expression>>>,
    pub direction: HeaderDirection,
    pub tags: Option<Parsed<Vec<Identifier>>>,
}

fn tags(
    tags: Option<Parsed<Vec<Identifier>>>,
    children: &mut Vec<AnnotationId>,
) -> Vec<Identifier> {
    let Some(tags) = tags else { return Vec::new() };
    children.push(tags.annotation);
    tags.value
}

impl ParseContext {
    pub fn signal_header(
        &mut self,
        span: Span,
        direction: HeaderDirection,
        header_tags: Option<Parsed<Vec<Identifier>>>,
    ) -> Parsed<DeclarationKind> {
        let (direction, annotation) = direction.into_parts();
        let mut children = Vec::new();
        children.extend(annotation);
        let tags = tags(header_tags, &mut children);
        let form = match direction {
            DirectionSyntax::Before(_) => SourceForm::Feature(Version::new(2, 2, 0)),
            DirectionSyntax::After(_) | DirectionSyntax::Unspecified => SourceForm::Plain,
        };
        self.annotate(DeclarationKind::Signal { direction, tags }, span, children, form)
    }

    pub fn bus_header(&mut self, span: Span, parts: BusHeaderParts) -> Parsed<DeclarationKind> {
        let (direction, annotation) = parts.direction.into_parts();
        let mut children = Vec::new();
        if let DirectionSyntax::Before(_) = direction {
            children.extend(annotation);
        }
        children.push(parts.name.annotation);
        let arguments = arguments(parts.arguments, &mut children);
        if let DirectionSyntax::After(_) = direction {
            children.extend(annotation);
        }
        let tags = tags(parts.tags, &mut children);
        let kind = DeclarationKind::Bus { type_name: parts.name.value, arguments, direction, tags };
        self.annotate(kind, span, children, SourceForm::Feature(Version::new(2, 2, 0)))
    }
}
