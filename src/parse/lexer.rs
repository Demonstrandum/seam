use super::tokens::{self, Token, TokenStream};

use std::path::Path;
use std::{fmt, error::Error};

#[derive(Debug, Clone)]
pub struct LexError(Token, String);

impl fmt::Display for LexError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[**] Lexical Error: `{}'.\nAt: {:#?}",
            self.1, self.0)
    }
}

impl Error for LexError { }

fn character_kind(character : char, prev : Option<tokens::Kind>)
    -> Option<tokens::Kind> {
    let kind = match character {
        '\n' | '\r' | ' ' | '\t' => None,
        '(' => Some(tokens::Kind::LParen),
        ')' => Some(tokens::Kind::RParen),
        '0'..='9' => Some(tokens::Kind::Number),
        ':' => Some(tokens::Kind::Keyword),
        '"' => Some(tokens::Kind::String),
        _ => Some(tokens::Kind::Symbol)
    };

    if prev == Some(tokens::Kind::String) {
        if character == '"' {
            None
        } else {
            prev
        }
    } else {
        kind
    }
}

pub fn lex<P: AsRef<Path>>(string : String, _source : Option<P>)
    -> Result<TokenStream, LexError> {

    let eof = string.len();
    let mut lines : usize = 1;
    let mut bytes : usize = 0;
    let mut line_bytes : usize = 0;

    let mut accumulator : Vec<u8> = Vec::new();
    let mut tokens = Vec::new();

    let mut token_start : usize = 0;
    let mut current_kind = None;
    let mut old_kind = None;

    while bytes < eof {
        let current_byte = string.as_bytes()[bytes];

        if !string.is_char_boundary(bytes) {
            accumulator.push(current_byte);
            bytes += 1;
            line_bytes += 1;
            continue;
        }

        let character = current_byte as char;

        let mut prev_kind = current_kind;
        current_kind = character_kind(character, current_kind);

        let string_start = character == '"'
        && prev_kind != Some(tokens::Kind::String);
        if string_start {
            current_kind = None;
        }

        let mut peek_kind = if bytes == eof - 1 {
            None
        } else {
            let peek_char = string.as_bytes()[bytes + 1] as char;
            character_kind(peek_char, current_kind)
        };

        let was_lparen = current_kind == Some(tokens::Kind::LParen);
        let was_rparen = current_kind == Some(tokens::Kind::RParen);
        let peek_rparen = peek_kind == Some(tokens::Kind::RParen);
        if was_lparen || was_rparen {
            peek_kind = None;
            prev_kind = None;
        }
        if peek_rparen {
            peek_kind = None;
        }

        if let Some(kind_current) = current_kind {
            if prev_kind.is_none() {
                old_kind = current_kind;
                token_start = line_bytes;
            }
            accumulator.push(current_byte);
            bytes += 1;
            line_bytes += 1;

            if peek_kind.is_none() {
                let kind = if let Some(kind_old) = old_kind {
                    kind_old
                } else {
                    kind_current
                };

                let mut span = accumulator.len();
                if kind == tokens::Kind::String {
                    span += 2;
                }

                let value = String::from_utf8(accumulator).unwrap();
                let site = tokens::Site::from_line(lines, token_start, span);
                tokens.push(Token::new(kind, value, site));
                accumulator = Vec::new();

                if was_lparen || peek_rparen || was_rparen {
                    old_kind = None;
                    current_kind = None;
                    token_start = line_bytes;
                }

            }
        } else {
            bytes += 1;
            line_bytes += 1;
        }

        if character == '\n' {
            line_bytes = 0;
            token_start = 0;
            lines += 1;
        }
        if string_start {
            current_kind = Some(tokens::Kind::String);
            old_kind = current_kind;
            token_start = line_bytes - 1;
        }
    }

    Ok(tokens)
}
