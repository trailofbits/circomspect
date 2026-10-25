//! Temporary bridge for the expression production family; removed with typed expressions.

use lalrpop_util::ParseError;

use crate::new_frontend::ast::{SyntaxDiagnostic, SyntaxKind, SyntaxNode, Version};
use crate::new_frontend::lexer::TokenKind;
use crate::new_frontend::parsed::{ParseContext, Parsed, SourceForm};
use crate::new_frontend::typed::{expression, Expression};

fn source_form(node: &SyntaxNode) -> SourceForm {
    match node.kind {
        SyntaxKind::Name | SyntaxKind::Call | SyntaxKind::Group | SyntaxKind::Ternary => {
            SourceForm::PotentialBus
        }
        SyntaxKind::AnonymousCall => SourceForm::AnonymousCall,
        SyntaxKind::Array => SourceForm::Array,
        SyntaxKind::Tuple => SourceForm::Tuple,
        SyntaxKind::Parallel => SourceForm::Feature(Version::new(2, 0, 8)),
        SyntaxKind::NamedInput(_) => SourceForm::Feature(Version::new(2, 1, 1)),
        SyntaxKind::Identifier if node.text.as_deref() == Some("_") => {
            SourceForm::Feature(Version::new(2, 1, 0))
        }
        SyntaxKind::Parameters
        | SyntaxKind::Inputs
        | SyntaxKind::Identifier
        | SyntaxKind::Number
        | SyntaxKind::Access
        | SyntaxKind::Unary(_)
        | SyntaxKind::Binary(_) => SourceForm::Plain,
    }
}

impl ParseContext {
    pub fn expression(
        &mut self,
        node: SyntaxNode,
    ) -> Result<Parsed<Expression>, ParseError<usize, TokenKind, SyntaxDiagnostic>> {
        let annotation = self.expression_annotations(&node);
        let value = expression(node).map_err(|error| ParseError::User { error })?;
        Ok(Parsed { value, annotation })
    }

    fn expression_annotations(
        &mut self,
        root: &SyntaxNode,
    ) -> crate::new_frontend::parsed::AnnotationId {
        enum Frame<'a> {
            Enter(&'a SyntaxNode),
            Finish(&'a SyntaxNode),
        }
        let mut work = vec![Frame::Enter(root)];
        let mut results = Vec::new();
        while let Some(frame) = work.pop() {
            match frame {
                Frame::Enter(node) => {
                    work.push(Frame::Finish(node));
                    for child in node.children.iter().rev() {
                        work.push(Frame::Enter(child));
                    }
                }
                Frame::Finish(node) => {
                    let children = results.split_off(results.len() - node.children.len());
                    let parsed = self.annotate((), node.span, children, source_form(node));
                    results.push(parsed.annotation);
                }
            }
        }
        // Every entered node emits one result; the final result is the visited root.
        results[0]
    }
}
