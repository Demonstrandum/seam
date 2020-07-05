use super::tokens::{self, Site, Token, TokenStream};

use std::rc::Rc;
use std::path::Path;
use std::{fmt, error::Error};

#[derive(Debug, Clone)]
pub struct LexError(Site, String);

impl fmt::Display for LexError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[**] Lexical Error {}: {}",
            self.0, self.1)
    }
}

impl Error for LexError { }

fn is_whitespace(character : char) -> bool {
    ['\n', '\r', '\t', ' '].contains(&character)
}

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

// TODO: Post-tokeniser parenthesis balancer, give
// nice and exact error messages.

pub fn lex<P: AsRef<Path>>(string : String, source : Option<P>)
    -> Result<TokenStream, LexError> {

    let eof = string.len();
    let mut lines : usize = 1;
    let mut bytes : usize = 0;
    let mut line_bytes : usize = 0;

    let source_str = source.map(
        |e| Rc::from(e.as_ref().display().to_string()));

    let mut accumulator : Vec<u8> = Vec::new();
    let mut tokens : TokenStream = Vec::new();

    let mut token_start : usize = 0;
    let mut current_kind = None;
    let mut old_kind = None;
    let mut string_open = false;
    let mut escaped = false;

    while bytes < eof {
        let current_byte = string.as_bytes()[bytes];

        if !string.is_char_boundary(bytes) {
            accumulator.push(current_byte);
            bytes += 1;
            line_bytes += 1;
            continue;
        }

        let character = current_byte as char;

        // Tripple quoted string:
        if character == '"'
        && string.get(bytes..bytes + 3) == Some("\"\"\"") {
            token_start = line_bytes;
            let start_line = lines;
            bytes += 3;
            line_bytes += 3;

            let mut found_end_quote = false;

            while let Some(quote) = string.get(bytes..bytes + 3) {
                if quote == "\"\"\"" {
                    found_end_quote = true;
                    break;
                }

                let c = string.as_bytes()[bytes];
                if c == '\n' as u8 {
                    lines += 1;
                    line_bytes = 0;
                }
                accumulator.push(c);
                bytes += 1;
                line_bytes += 1;
            }

            if !found_end_quote {
                let mut site = Site::from_line(
                    lines, line_bytes, 1);
                site.source = source_str.clone();
                return Err(LexError(site,
                    String::from("Unclosed tripple-quoted string.")));
            }


            bytes += 3;
            line_bytes += 3;
            current_kind = None;

            let span = accumulator.len() + 3 + 3;
            let mut site = Site::from_line(start_line,
                token_start, span);
            site.source = source_str.clone();
            tokens.push(Token::new(tokens::Kind::String,
                String::from_utf8(accumulator).unwrap(),
                site));
            accumulator = Vec::new();
            continue;
        }

        if character == '\\' {  // Escapes
            if current_kind == Some(tokens::Kind::String) {
                // How escapes work in strings (TODO)
            } else {
                // How they work outside strings:
                // TODO: add more escapes.
                if bytes + 1 == eof {
                    continue;
                }
                match string.as_bytes()[bytes + 1] as char {
                    '\n' | '\r' | ' ' | '\t' => {
                        current_kind = None;
                        bytes += 1;
                        line_bytes += 1;
                    },
                    _ => ()
                }
                escaped = true;
                bytes += 1;
                line_bytes += 1;
                continue;
            }
        }

        // EON Comments:
        if character == ';' && current_kind != Some(tokens::Kind::String) {
            let mut i = 0;
            while bytes < eof
            && string.as_bytes()[bytes + i] != '\n' as u8 {
                i += 1;
            }
            bytes += i;
            continue;
        }

        let mut prev_kind = current_kind;
        current_kind = character_kind(character, current_kind);
        if escaped {
            current_kind = Some(tokens::Kind::Symbol);
        }

        let string_start = character == '"'
            && prev_kind != Some(tokens::Kind::String)
            && !escaped;
        if string_start {
            string_open = true;
            current_kind = None;
        }

        let peek_char = if bytes == eof - 1 {
            None
        } else {
            let peek_char = string.as_bytes()[bytes + 1] as char;
            Some(peek_char)
        };
        let mut peek_kind = if let Some(peeked) = peek_char {
            character_kind(peeked, current_kind)
        } else { None };

        let some_lparen = Some(tokens::Kind::LParen);
        let some_rparen = Some(tokens::Kind::RParen);

        let was_lparen = current_kind == some_lparen;
        let was_rparen = current_kind == some_rparen;

        let peek_string = peek_char == Some('"');
        let peek_lparen = peek_kind == some_lparen;
        let peek_rparen = peek_kind == some_rparen;

        if was_lparen || was_rparen {
            peek_kind = None;
            prev_kind = None;
        } else if peek_rparen || peek_lparen {
            peek_kind = None;
        } else if peek_string {
            peek_kind = None;
            string_open = false;
        }

        // If we're on a whitespace, and there's a bracket (or quote) ahead,
        // we need to explicitly say there's whitespace between the
        // last token and the next bracket/quotation.
        // (Ignore the whitespace, if it is consecutive to another whitespace)
        match tokens.last() {
            Some(token) if token.kind != tokens::Kind::Whitespace
                        && token.kind != tokens::Kind::Keyword
                        && is_whitespace(character)
                        && (peek_rparen
                         || peek_lparen
                         || peek_char == Some('"')
                         || token.kind == tokens::Kind::String
                         || token.kind == tokens::Kind::RParen) => {
                let kind = tokens::Kind::Whitespace;
                let mut site = Site::from_line(lines, line_bytes, 1);
                site.source = source_str.clone();
                let value = character.to_string();
                tokens.push(Token::new(kind, value, site));
            },
            Some(_) | None => (),
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
                let mut site = Site::from_line(lines, token_start, span);
                site.source = source_str.clone();
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
        escaped = false;
    }
    if string_open {
        let mut site = Site::from_line(lines, line_bytes, 1);
        site.source = source_str.clone();
        return Err(LexError(site,
            "Unclosed double-quoted string.".to_string()))
    }
    Ok(tokens)
}
