//! Byte-level tokenizer for OWL Manchester Syntax.
//!
//! Adapted from OxiRS `oxirs-rule/src/manchester/lexer.rs` (Apache-2.0; see NOTICE),
//! extended for the document grammar our artifacts require:
//!   - full IRIs in angle brackets (`<https://…#Local>`) → [`Token::Iri`]
//!   - string literals (`"…"` with `\"`/`\\` escapes; a trailing `@lang` or
//!     `^^datatype` suffix is consumed and dropped) → [`Token::Str`]
//!   - commas (Manchester section lists are separate axioms) → [`Token::Comma`]
//!   - identifier bodies additionally admit `-` and `.` (prefixed locals)
//!
//! Keywords are case-sensitive per the W3C grammar: `and`, `or`, `not`, `some`,
//! `only`, `min`, `max`, `exactly`, `value`, `Self`, `that`.
//! Data-range facets (`[...]`) are refused loudly — out of the v0 grammar.

use super::ManchesterError;

/// A single lexical token with grammar-relevant identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    /// Prefixed or bare name (`bfo:0000015`, `owl:Thing`, `Person`).
    Ident(String),
    /// Full IRI, angle brackets stripped.
    Iri(String),
    /// String literal, quotes stripped, escapes resolved; lang/datatype suffix dropped.
    Str(String),
    And,
    Or,
    Not,
    Some,
    Only,
    Min,
    Max,
    Exactly,
    Value,
    That,
    SelfKw,
    Comma,
    LBrace,
    RBrace,
    LParen,
    RParen,
    Number(u32),
    Eof,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Ident(s) => write!(f, "identifier `{s}`"),
            Token::Iri(s) => write!(f, "IRI `<{s}>`"),
            Token::Str(_) => write!(f, "string literal"),
            Token::And => write!(f, "`and`"),
            Token::Or => write!(f, "`or`"),
            Token::Not => write!(f, "`not`"),
            Token::Some => write!(f, "`some`"),
            Token::Only => write!(f, "`only`"),
            Token::Min => write!(f, "`min`"),
            Token::Max => write!(f, "`max`"),
            Token::Exactly => write!(f, "`exactly`"),
            Token::Value => write!(f, "`value`"),
            Token::That => write!(f, "`that`"),
            Token::SelfKw => write!(f, "`Self`"),
            Token::Comma => write!(f, "`,`"),
            Token::LBrace => write!(f, "`{{`"),
            Token::RBrace => write!(f, "`}}`"),
            Token::LParen => write!(f, "`(`"),
            Token::RParen => write!(f, "`)`"),
            Token::Number(n) => write!(f, "number `{n}`"),
            Token::Eof => write!(f, "end of input"),
        }
    }
}

fn classify_ident(raw: &str) -> Token {
    match raw {
        "and" => Token::And,
        "or" => Token::Or,
        "not" => Token::Not,
        "some" => Token::Some,
        "only" => Token::Only,
        "min" => Token::Min,
        "max" => Token::Max,
        "exactly" => Token::Exactly,
        "value" => Token::Value,
        "that" => Token::That,
        "Self" => Token::SelfKw,
        _ => Token::Ident(raw.to_string()),
    }
}

#[inline]
fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b':' || b == b'-' || b == b'.'
}

#[inline]
fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

/// Tokenize a Manchester expression/section body into `(Token, byte_offset)` pairs
/// with an [`Token::Eof`] sentinel appended.
pub fn tokenize(input: &str) -> Result<Vec<(Token, usize)>, ManchesterError> {
    let bytes = input.as_bytes();
    let len = bytes.len();
    let mut pos = 0usize;
    let mut tokens: Vec<(Token, usize)> = Vec::with_capacity(len / 3 + 8);

    while pos < len {
        if bytes[pos].is_ascii_whitespace() {
            pos += 1;
            continue;
        }
        let start = pos;
        let b = bytes[pos];

        if is_ident_start(b) {
            while pos < len && is_ident_char(bytes[pos]) {
                pos += 1;
            }
            tokens.push((classify_ident(&input[start..pos]), start));
        } else if b.is_ascii_digit() {
            while pos < len && bytes[pos].is_ascii_digit() {
                pos += 1;
            }
            let raw = &input[start..pos];
            let n: u32 = raw.parse().map_err(|_| ManchesterError::Lex {
                pos: start,
                msg: format!("integer literal `{raw}` overflows u32"),
            })?;
            tokens.push((Token::Number(n), start));
        } else if b == b'<' {
            pos += 1;
            let iri_start = pos;
            while pos < len && bytes[pos] != b'>' {
                pos += 1;
            }
            if pos >= len {
                return Err(ManchesterError::Lex {
                    pos: start,
                    msg: "unterminated `<…>` IRI".to_string(),
                });
            }
            tokens.push((Token::Iri(input[iri_start..pos].to_string()), start));
            pos += 1; // consume '>'
        } else if b == b'"' {
            pos += 1;
            // byte-accurate scan (escapes are ASCII), decoded as UTF-8 at the end so
            // multi-byte characters in labels survive intact
            let mut raw: Vec<u8> = Vec::new();
            loop {
                if pos >= len {
                    return Err(ManchesterError::Lex {
                        pos: start,
                        msg: "unterminated string literal".to_string(),
                    });
                }
                match bytes[pos] {
                    b'"' => {
                        pos += 1;
                        break;
                    }
                    b'\\' if pos + 1 < len => {
                        raw.push(bytes[pos + 1]);
                        pos += 2;
                    }
                    c => {
                        raw.push(c);
                        pos += 1;
                    }
                }
            }
            let s = String::from_utf8(raw).map_err(|_| ManchesterError::Lex {
                pos: start,
                msg: "string literal is not valid UTF-8".to_string(),
            })?;
            // consume-and-drop a language tag or datatype suffix
            if pos < len && bytes[pos] == b'@' {
                pos += 1;
                while pos < len && (bytes[pos].is_ascii_alphanumeric() || bytes[pos] == b'-') {
                    pos += 1;
                }
            } else if pos + 1 < len && bytes[pos] == b'^' && bytes[pos + 1] == b'^' {
                pos += 2;
                if pos < len && bytes[pos] == b'<' {
                    while pos < len && bytes[pos] != b'>' {
                        pos += 1;
                    }
                    pos += 1;
                } else {
                    while pos < len && is_ident_char(bytes[pos]) {
                        pos += 1;
                    }
                }
            }
            tokens.push((Token::Str(s), start));
        } else {
            pos += 1;
            match b {
                b',' => tokens.push((Token::Comma, start)),
                b'{' => tokens.push((Token::LBrace, start)),
                b'}' => tokens.push((Token::RBrace, start)),
                b'(' => tokens.push((Token::LParen, start)),
                b')' => tokens.push((Token::RParen, start)),
                b'[' => {
                    return Err(ManchesterError::Lex {
                        pos: start,
                        msg: "data-range facets `[…]` are out of the v0 grammar (refused, not approximated)"
                            .to_string(),
                    });
                }
                other => {
                    return Err(ManchesterError::Lex {
                        pos: start,
                        msg: format!("unexpected character `{}`", other as char),
                    });
                }
            }
        }
    }

    tokens.push((Token::Eof, len));
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iris_strings_and_commas_tokenize() {
        let toks = tokenize(
            r#"<https://signals.zndx.org/sdg#A> , bfo:0000015 and "a label"@en "typed"^^xsd:string"#,
        )
        .unwrap();
        assert!(matches!(&toks[0].0, Token::Iri(s) if s.ends_with("sdg#A")));
        assert!(matches!(&toks[1].0, Token::Comma));
        assert!(matches!(&toks[2].0, Token::Ident(s) if s == "bfo:0000015"));
        assert!(matches!(&toks[3].0, Token::And));
        assert!(matches!(&toks[4].0, Token::Str(s) if s == "a label"));
        assert!(matches!(&toks[5].0, Token::Str(s) if s == "typed"));
    }

    #[test]
    fn facets_refuse_loudly() {
        let err = tokenize("xsd:integer[>= 0]").unwrap_err();
        assert!(err.to_string().contains("facets"));
    }

    #[test]
    fn multibyte_utf8_survives_string_literals() {
        let toks = tokenize(r#""élan vital""#).unwrap();
        assert!(matches!(&toks[0].0, Token::Str(s) if s == "élan vital"));
    }
}
