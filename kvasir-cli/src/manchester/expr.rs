//! Recursive-descent parser for OWL Manchester class expressions.
//!
//! Adapted from OxiRS `oxirs-rule/src/manchester/parser.rs` (Apache-2.0; see NOTICE).
//! Grammar (precedence: `or` < `and`/`that` < `not` < restrictions/primaries):
//!
//! ```text
//! expr_list := expr (',' expr)*
//! expr      := or_expr
//! or_expr   := and_expr (('or') and_expr)*
//! and_expr  := not_expr (('and' | 'that') not_expr)*
//! not_expr  := 'not' primary | primary
//! primary   := name rest
//!            | '{' name+ '}'
//!            | '(' expr ')'
//! name      := Ident | Iri
//! rest      := 'some' primary | 'only' primary
//!            | ('min'|'max'|'exactly') Number primary?
//!            | 'value' name | 'Self'
//!            | ε                         → Named(name)
//! ```
//!
//! Extensions over the OxiRS source: full-IRI primaries, `that` as a conjunction
//! keyword (W3C grammar sugar), `Self` refused with a named reason (out of the DDL
//! fragment), and `expr_list` for Manchester section lists (comma = separate axioms).

use super::lexer::{tokenize, Token};
use super::{Expr, ManchesterError};

struct Parser {
    tokens: Vec<(Token, usize)>,
    cursor: usize,
}

impl Parser {
    fn new(tokens: Vec<(Token, usize)>) -> Self {
        Self { tokens, cursor: 0 }
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.cursor].0
    }

    fn advance(&mut self) {
        if self.cursor + 1 < self.tokens.len() {
            self.cursor += 1;
        }
    }

    fn consume(&mut self) -> Token {
        let tok = self.tokens[self.cursor].0.clone();
        self.advance();
        tok
    }

    fn err(&self, msg: impl Into<String>) -> ManchesterError {
        ManchesterError::Parse {
            pos: self.cursor,
            msg: msg.into(),
        }
    }

    /// A `name` is a prefixed identifier or a full IRI; returns its string form.
    fn maybe_name(&mut self) -> Option<String> {
        match self.peek() {
            Token::Ident(_) | Token::Iri(_) => match self.consume() {
                Token::Ident(s) | Token::Iri(s) => Some(s),
                _ => unreachable!(),
            },
            _ => None,
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, ManchesterError> {
        self.parse_or_expr()
    }

    fn parse_or_expr(&mut self) -> Result<Expr, ManchesterError> {
        let first = self.parse_and_expr()?;
        if !matches!(self.peek(), Token::Or) {
            return Ok(first);
        }
        let mut arms = vec![first];
        while matches!(self.peek(), Token::Or) {
            self.advance();
            arms.push(self.parse_and_expr()?);
        }
        Ok(Expr::Or(arms))
    }

    fn parse_and_expr(&mut self) -> Result<Expr, ManchesterError> {
        let first = self.parse_not_expr()?;
        if !matches!(self.peek(), Token::And | Token::That) {
            return Ok(first);
        }
        let mut arms = vec![first];
        while matches!(self.peek(), Token::And | Token::That) {
            self.advance();
            arms.push(self.parse_not_expr()?);
        }
        Ok(Expr::And(arms))
    }

    fn parse_not_expr(&mut self) -> Result<Expr, ManchesterError> {
        if matches!(self.peek(), Token::Not) {
            self.advance();
            let inner = self.parse_primary()?;
            return Ok(Expr::Not(Box::new(inner)));
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Result<Expr, ManchesterError> {
        match self.peek().clone() {
            Token::Ident(_) | Token::Iri(_) => {
                let name = self.maybe_name().expect("peeked");
                self.parse_rest(name)
            }
            Token::LBrace => {
                self.advance();
                let mut individuals: Vec<String> = Vec::new();
                loop {
                    match self.peek().clone() {
                        Token::RBrace => {
                            self.advance();
                            break;
                        }
                        Token::Ident(_) | Token::Iri(_) => {
                            individuals.push(self.maybe_name().expect("peeked"));
                        }
                        Token::Comma => {
                            self.advance(); // `{a, b}` — commas between individuals are legal
                        }
                        Token::Eof => {
                            return Err(self.err("unexpected end of input inside `{…}`"));
                        }
                        other => {
                            return Err(self.err(format!(
                                "expected individual or `}}` inside `{{…}}`, got {other}"
                            )));
                        }
                    }
                }
                if individuals.is_empty() {
                    return Err(self.err("`{…}` must contain at least one individual"));
                }
                Ok(Expr::OneOf(individuals))
            }
            Token::LParen => {
                self.advance();
                let inner = self.parse_expr()?;
                match self.peek() {
                    Token::RParen => {
                        self.advance();
                    }
                    other => return Err(self.err(format!("expected `)`, got {other}"))),
                }
                Ok(inner)
            }
            Token::Eof => Err(self.err("unexpected end of input — expected a class expression")),
            other => Err(self.err(format!("expected a name, `{{`, or `(`, got {other}"))),
        }
    }

    fn parse_rest(&mut self, property: String) -> Result<Expr, ManchesterError> {
        match self.peek().clone() {
            Token::Some => {
                self.advance();
                Ok(Expr::Some {
                    property,
                    filler: Box::new(self.parse_primary()?),
                })
            }
            Token::Only => {
                self.advance();
                Ok(Expr::Only {
                    property,
                    filler: Box::new(self.parse_primary()?),
                })
            }
            Token::Min => {
                self.advance();
                let n = self.expect_number()?;
                Ok(Expr::Min {
                    property,
                    n,
                    filler: self.maybe_primary()?.map(Box::new),
                })
            }
            Token::Max => {
                self.advance();
                let n = self.expect_number()?;
                Ok(Expr::Max {
                    property,
                    n,
                    filler: self.maybe_primary()?.map(Box::new),
                })
            }
            Token::Exactly => {
                self.advance();
                let n = self.expect_number()?;
                Ok(Expr::Exactly {
                    property,
                    n,
                    filler: self.maybe_primary()?.map(Box::new),
                })
            }
            Token::Value => {
                self.advance();
                let individual = self
                    .maybe_name()
                    .ok_or_else(|| self.err("expected an individual name after `value`"))?;
                Ok(Expr::HasValue {
                    property,
                    individual,
                })
            }
            Token::SelfKw => Err(self.err(
                "`Self` restrictions are out of the v0 fragment (refused, not approximated)",
            )),
            _ => Ok(Expr::Named(property)),
        }
    }

    fn expect_number(&mut self) -> Result<u32, ManchesterError> {
        match self.peek().clone() {
            Token::Number(n) => {
                self.advance();
                Ok(n)
            }
            other => Err(self.err(format!("expected a number, got {other}"))),
        }
    }

    fn maybe_primary(&mut self) -> Result<Option<Expr>, ManchesterError> {
        match self.peek() {
            Token::Ident(_) | Token::Iri(_) | Token::LBrace | Token::LParen => {
                Ok(Some(self.parse_primary()?))
            }
            _ => Ok(None),
        }
    }
}

/// Parse one class expression; the whole input must be consumed.
#[allow(dead_code)] // single-expression API — the verbalise module's entry point (next increment)
pub fn parse(input: &str) -> Result<Expr, ManchesterError> {
    let mut items = parse_list(input)?;
    if items.len() != 1 {
        return Err(ManchesterError::Parse {
            pos: 0,
            msg: format!("expected one expression, found a list of {}", items.len()),
        });
    }
    Ok(items.remove(0))
}

/// Parse a Manchester SECTION body: comma-separated expressions (each a separate axiom).
pub fn parse_list(input: &str) -> Result<Vec<Expr>, ManchesterError> {
    if input.trim().is_empty() {
        return Err(ManchesterError::Parse {
            pos: 0,
            msg: "input is empty — expected a class expression".to_string(),
        });
    }
    let tokens = tokenize(input)?;
    let mut parser = Parser::new(tokens);
    let mut items = vec![parser.parse_expr()?];
    loop {
        match parser.peek() {
            Token::Comma => {
                parser.advance();
                items.push(parser.parse_expr()?);
            }
            Token::Eof => break,
            other => {
                return Err(parser.err(format!(
                    "unexpected token {other} after expression — expected `,` or end of input"
                )));
            }
        }
    }
    Ok(items)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn precedence_and_nesting() {
        let e = parse("A and p some (B or C) and not D").unwrap();
        let Expr::And(parts) = e else { panic!("expected And") };
        assert_eq!(parts.len(), 3);
        assert!(matches!(&parts[0], Expr::Named(n) if n == "A"));
        assert!(matches!(&parts[1], Expr::Some { filler, .. } if matches!(**filler, Expr::Or(_))));
        assert!(matches!(&parts[2], Expr::Not(_)));
    }

    #[test]
    fn comma_lists_are_separate_axioms() {
        let items =
            parse_list("bfo:0000023, sdg:inheresIn exactly 1 <https://x.org/sdg#A>, sdg:realizes some B")
                .unwrap();
        assert_eq!(items.len(), 3);
        assert!(matches!(&items[1], Expr::Exactly { n: 1, .. }));
    }

    #[test]
    fn that_is_conjunction_sugar() {
        let e = parse("Person that hasChild some Person").unwrap();
        assert!(matches!(e, Expr::And(parts) if parts.len() == 2));
    }

    #[test]
    fn self_refuses_by_name() {
        assert!(parse("likes Self").is_err());
    }

    #[test]
    fn nested_restriction_filler() {
        let e = parse("p some (q some R)").unwrap();
        let Expr::Some { filler, .. } = e else { panic!() };
        assert!(matches!(*filler, Expr::Some { .. }));
    }
}
