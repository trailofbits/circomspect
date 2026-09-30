use super::errors::{ParsingError, UnclosedCommentError};
use super::lang;

use program_structure::ast::AST;
use program_structure::report::Report;
use program_structure::report::ReportCollection;
use program_structure::file_definition::FileID;
use std::ops::Range;

#[derive(Clone, Debug)]
pub enum ParserUserError {
    VersionOverflow(Range<usize>),
}

pub fn preprocess(expr: &str, file_id: FileID) -> Result<String, Box<Report>> {
    let mut pp = String::new();
    let mut state = 0;
    let mut loc = 0;
    let mut block_start = 0;

    let mut it = expr.chars();
    while let Some(c0) = it.next() {
        loc += 1;
        match (state, c0) {
            (0, '/') => {
                loc += 1;
                match it.next() {
                    Some('/') => {
                        state = 1;
                        pp.push(' ');
                        pp.push(' ');
                    }
                    Some('*') => {
                        block_start = loc;
                        state = 2;
                        pp.push(' ');
                        pp.push(' ');
                    }
                    Some(c1) => {
                        pp.push(c0);
                        pp.push(c1);
                    }
                    None => {
                        pp.push(c0);
                        break;
                    }
                }
            }
            (0, _) => pp.push(c0),
            (1, '\n') => {
                pp.push(c0);
                state = 0;
            }
            (2, '*') => {
                loc += 1;
                match it.next() {
                    Some('/') => {
                        pp.push(' ');
                        pp.push(' ');
                        state = 0;
                    }
                    Some(c) => {
                        pp.push(' ');
                        for _i in 0..c.len_utf8() {
                            pp.push(' ');
                        }
                    }
                    None => {
                        let error =
                            UnclosedCommentError { location: block_start..block_start, file_id };
                        return Err(Box::new(error.into_report()));
                    }
                }
            }
            (_, c) => {
                for _i in 0..c.len_utf8() {
                    pp.push(' ');
                }
            }
        }
    }
    Ok(pp)
}

pub fn parse_file(src: &str, file_id: FileID) -> Result<(AST, ReportCollection), Box<Report>> {
    let src = preprocess(src, file_id)?;
    let mut errors = Vec::new();
    let mut ast = lang::ParseAstParser::new()
        .parse(&mut errors, &src)
        .map_err(|error| Box::new(parse_error_report(error, file_id)))?;
    for include in &mut ast.includes {
        include.meta.set_file_id(file_id);
    }
    let reports =
        errors.into_iter().map(|error| parse_error_report(error.error, file_id)).collect();
    Ok((ast, reports))
}

fn parse_error_report(
    parse_error: lalrpop_util::ParseError<usize, lang::Token<'_>, ParserUserError>,
    file_id: FileID,
) -> Report {
    use lalrpop_util::ParseError::*;
    let error = match parse_error {
        InvalidToken { location } => ParsingError {
            file_id,
            message: "Invalid token found.".to_string(),
            location: location..location,
        },
        UnrecognizedEof { location, ref expected } => ParsingError {
            file_id,
            message: format!("Unexpected end of file.{}", format_expected(expected)),
            location: location..location,
        },
        UnrecognizedToken { ref token, ref expected } => ParsingError {
            file_id,
            message: format!(
                "Unrecognized token `{}` found.{}",
                token.1,
                format_expected(expected)
            ),
            location: token.0..token.2,
        },
        ExtraToken { ref token } => ParsingError {
            file_id,
            message: format!("Extra token `{}` found.", token.2),
            location: token.0..token.2,
        },
        User { error: ParserUserError::VersionOverflow(location) } => ParsingError {
            file_id,
            message: "A version component is too large.".to_string(),
            location,
        },
    };
    error.into_report()
}

pub fn parse_string(src: &str) -> Option<AST> {
    let src = preprocess(src, 0).ok()?;
    let mut errors = Vec::new();
    let ast = lang::ParseAstParser::new().parse(&mut errors, &src).ok()?;
    errors.is_empty().then_some(ast)
}

/// Parse a single (function or template) definition for testing purposes.
use program_structure::ast::Definition;

pub fn parse_definition(src: &str) -> Option<Definition> {
    match parse_string(src) {
        Some(AST { mut definitions, .. }) if definitions.len() == 1 => definitions.pop(),
        _ => None,
    }
}

#[must_use]
fn format_expected(tokens: &[String]) -> String {
    if tokens.is_empty() {
        String::new()
    } else {
        let tokens = tokens
            .iter()
            .enumerate()
            .map(|(index, token)| {
                if index == 0 {
                    token.replace('\"', "`")
                } else if index < tokens.len() - 1 {
                    format!(", {}", token.replace('\"', "`"))
                } else {
                    format!(" or {}", token.replace('\"', "`"))
                }
            })
            .collect::<Vec<_>>()
            .join("");
        format!(" Expected one of {tokens}.")
    }
}

#[cfg(test)]
mod tests {
    use super::parse_string;

    #[test]
    fn parse_string_rejects_recovered_errors() {
        assert!(parse_string("template Broken() { var value = ; }").is_none());
        assert!(parse_string("template Broken() { var value = @; }").is_none());
    }

    #[test]
    fn test_parse_string() {
        let function = r#"
            function f(m) {
                // This is a comment.
                var x = 1024;
                var y = 16;
                while (x < m) {
                    x += y;
                }
                if (x == m) {
                    x = 0;
                }
                /* This is another comment. */
                return x;
            }
        "#;
        let _ = parse_string(function);

        let template = r#"
            template T(m) {
                signal input in[m];
                signal output out;

                var sum = 0;
                for (var i = 0; i < m; i++) {
                    sum += in[i];
                }
                out <== sum;
            }
        "#;
        let _ = parse_string(template);
    }
}
