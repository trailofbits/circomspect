use crate::new_frontend::ast::Span;
use crate::new_frontend::parsed::{unpack, ParseContext, Parsed, SourceForm};
use crate::new_frontend::typed::{Access, AnonymousCallExpr, AnonymousInput, Expression, Identifier};

pub(crate) struct AnonymousParts {
    pub name: Parsed<Identifier>,
    pub parameters: Parsed<Vec<Expression>>,
    pub inputs: Parsed<Vec<AnonymousInput>>,
}

impl ParseContext {
    pub fn variable(
        &mut self,
        span: Span,
        name: Parsed<Identifier>,
        access: Vec<Parsed<Access>>,
    ) -> Parsed<Expression> {
        let (access, access_children) = unpack(access);
        let mut children = vec![name.annotation];
        children.extend(access_children);
        self.annotate(
            Expression::Name { identifier: name.value, access, span },
            span,
            children,
            SourceForm::PotentialBus,
        )
    }

    pub fn call(
        &mut self,
        span: Span,
        name: Parsed<Identifier>,
        arguments: Vec<Parsed<Expression>>,
    ) -> Parsed<Expression> {
        let (arguments, argument_children) = unpack(arguments);
        let mut children = vec![name.annotation];
        children.extend(argument_children);
        self.annotate(
            Expression::Call { name: name.value, arguments, span },
            span,
            children,
            SourceForm::PotentialBus,
        )
    }

    pub fn anonymous_call(&mut self, span: Span, parts: AnonymousParts) -> Parsed<Expression> {
        let children =
            vec![parts.name.annotation, parts.parameters.annotation, parts.inputs.annotation];
        let call = AnonymousCallExpr {
            name: parts.name.value,
            parameters: parts.parameters.value,
            inputs: parts.inputs.value,
            span,
        };
        self.annotate(Expression::AnonymousCall(call), span, children, SourceForm::AnonymousCall)
    }
}
