use super::errors::{ParsingError, UnclosedCommentError};
use super::lang;

use program_structure::ast::AST;
use program_structure::report::Report;
use program_structure::report::ReportCollection;
use program_structure::file_definition::FileID;
use std::iter::Peekable;
use std::ops::Range;
use std::str::CharIndices;

#[derive(Clone, Debug)]
pub enum ParserUserError {
    VersionOverflow(Range<usize>),
}

#[derive(Clone, Copy)]
enum ScanState {
    Code,
    String,
    LineComment,
    BlockComment { start: usize },
}

fn mask_char(output: &mut String, character: char) {
    if character == '\n' {
        output.push('\n');
    } else {
        for _ in 0..character.len_utf8() {
            output.push(' ');
        }
    }
}

fn scan_code(
    index: usize,
    character: char,
    chars: &mut Peekable<CharIndices<'_>>,
    output: &mut String,
) -> ScanState {
    match (character, chars.peek()) {
        ('"', _) => {
            output.push(character);
            ScanState::String
        }
        ('/', Some((_, '/'))) => {
            output.push_str("  ");
            let _ = chars.next();
            ScanState::LineComment
        }
        ('/', Some((_, '*'))) => {
            output.push_str("  ");
            let _ = chars.next();
            ScanState::BlockComment { start: index }
        }
        _ => {
            output.push(character);
            ScanState::Code
        }
    }
}

fn scan_block_comment(
    start: usize,
    character: char,
    chars: &mut Peekable<CharIndices<'_>>,
    output: &mut String,
) -> ScanState {
    if character == '*' {
        if let Some((_, '/')) = chars.peek() {
            output.push_str("  ");
            let _ = chars.next();
            return ScanState::Code;
        }
    }
    mask_char(output, character);
    ScanState::BlockComment { start }
}

pub fn preprocess(src: &str, file_id: FileID) -> (String, ReportCollection) {
    let mut output = String::with_capacity(src.len());
    let mut state = ScanState::Code;
    let mut chars = src.char_indices().peekable();
    while let Some((index, character)) = chars.next() {
        state = match state {
            ScanState::Code => scan_code(index, character, &mut chars, &mut output),
            ScanState::String => {
                output.push(character);
                if character == '"' {
                    ScanState::Code
                } else {
                    ScanState::String
                }
            }
            ScanState::LineComment => {
                mask_char(&mut output, character);
                if character == '\n' {
                    ScanState::Code
                } else {
                    ScanState::LineComment
                }
            }
            ScanState::BlockComment { start } => {
                scan_block_comment(start, character, &mut chars, &mut output)
            }
        };
    }
    let reports = match state {
        ScanState::BlockComment { start } => {
            let error = UnclosedCommentError { location: start..start + 2, file_id };
            vec![error.into_report()]
        }
        ScanState::Code | ScanState::String | ScanState::LineComment => Vec::new(),
    };
    debug_assert_eq!(output.len(), src.len());
    (output, reports)
}

pub fn parse_file(src: &str, file_id: FileID) -> Result<(AST, ReportCollection), Box<Report>> {
    let (src, mut reports) = preprocess(src, file_id);
    let mut errors = Vec::new();
    let mut ast = lang::ParseAstParser::new()
        .parse(&mut errors, &src)
        .map_err(|error| Box::new(parse_error_report(error, file_id)))?;
    for include in &mut ast.includes {
        include.meta.set_file_id(file_id);
    }
    reports.extend(errors.into_iter().map(|error| parse_error_report(error.error, file_id)));
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
    let (src, reports) = preprocess(src, 0);
    if !reports.is_empty() {
        return None;
    }
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
    use super::{parse_string, preprocess};

    #[test]
    fn preprocess_preserves_byte_offsets_and_quoted_comment_markers() {
        let source = "include \"a//b/*c\"; /* π */ template T() {}";
        let (output, reports) = preprocess(source, 0);

        assert!(reports.is_empty());
        assert_eq!(output.len(), source.len());
        assert!(output.contains("include \"a//b/*c\";"));
        assert_eq!(output.find("template"), source.find("template"));
    }

    #[test]
    fn parse_string_rejects_unclosed_comment() {
        assert!(parse_string("template T() {} /* unfinished").is_none());
    }

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
