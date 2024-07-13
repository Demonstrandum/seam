use super::tokens::{self, Site, Token};

use std::str::pattern::Pattern;
use std::{fmt, error::Error};
use std::cell::Cell;

use unicode_width::UnicodeWidthStr;

#[derive(Debug, Clone)]
pub struct LexError<'a>(pub String, pub Site<'a>);

impl<'a> fmt::Display for LexError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let LexError(msg, site) = self;
        let line_prefix = format!("  {} |", site.line);
        let line_view = site.line_slice();
        writeln!(f, "{} {}", line_prefix, line_view)?;
        writeln!(f, "{:>prefix_offset$} {:~>text_offset$}{:^>length$}", "|", "", "",
            prefix_offset=UnicodeWidthStr::width(line_prefix.as_str()),
            text_offset=site.line_column() - 1,
            length=site.width())?;
        write!(f, "[**] Lexical Error {}: {}", site, msg)
    }
}

impl<'a> Error for LexError<'a> { }

fn is_whitespace(character: char) -> bool {
    ['\n', '\r', '\t', ' '].contains(&character)
}

fn character_kind(character: char)
    -> Option<tokens::Kind> {
    match character {
        '\n' | '\r' | ' ' | '\t' => None,
        '('       => Some(tokens::Kind::LParen),
        ')'       => Some(tokens::Kind::RParen),
        '0'..='9' => Some(tokens::Kind::Number),
        '-'       => Some(tokens::Kind::Number),
        ':'       => Some(tokens::Kind::Keyword),
        '"'       => Some(tokens::Kind::String),
        _         => Some(tokens::Kind::Symbol)
    }
}

/// Lexer moves source-code string into itself,
/// and references it when generating tokens.
#[derive(Debug, Clone)]
pub struct Lexer {
    pub source_path: String,
    pub source: String,
    line: Cell<usize>,
    byte_offset: Cell<usize>,
    byte_offset_line: Cell<usize>,
}

impl<'a> Lexer {
    pub fn new(source_path: String, source: String) -> Self {
        Self {
            source_path,
            source,
            line: Cell::new(1),
            byte_offset: Cell::new(0),
            byte_offset_line: Cell::new(0),
        }
    }

    pub fn get_source(&self) -> &str {
        &self.source
    }

    fn increment_byte_offsets(&self, offset: usize) {
        let i = self.byte_offset.get();
        let j = self.byte_offset_line.get();
        self.byte_offset.set(i + offset);
        self.byte_offset_line.set(j + offset);
    }

    fn next_line(&self) {
        let l = self.line.get();
        self.line.set(l + 1);
        self.byte_offset_line.set(0);
    }

    /// Advance the lexer past any whitespace characters,
    /// and ignore any comments.
    fn consume_whitespace(&'a self) -> &'a str {
        let bytes = self.source.as_bytes();
        let mut start = self.byte_offset.get();
        if start >= bytes.len() {
            return "";
        }
        let mut inside_eon_comment: bool = false;
        loop {
            let index = self.byte_offset.get();
            let byte: u8 = bytes[index];
            if byte as char == ';' {
                inside_eon_comment = true;
            }
            if !is_whitespace(byte as char) && !inside_eon_comment {
                break;
            }
            self.increment_byte_offsets(1);
            if self.byte_offset.get() >= bytes.len() {
                break;
            }
            if byte as char == '\n' {
                self.next_line();
                if inside_eon_comment {
                    // EON comments ends at end-of-line.
                    inside_eon_comment = false;
                    // Now, whitespace is only what comes *after* the comment.
                    start = index;
                }
            }
        }
        unsafe {
            std::str::from_utf8_unchecked(&bytes[start..self.byte_offset.get()])
        }
    }

    /// Look at immediately following complete character.
    /// Returns `None` if file is at EOF.
    fn peek_char(&self) -> Option<char> {
        let bytes = self.source.as_bytes();
        let slice = &bytes[self.byte_offset.get()..];
        unsafe {
            let utf8 = std::str::from_utf8_unchecked(slice);
            let mut chars = utf8.chars();
            chars.next()
        }
    }

    /// Check if source-code at current possition starts with a pattern.
    fn starts_with<P>(&'a self, pat: P) -> bool where P: Pattern<'a> {
        self.source[self.byte_offset.get()..].starts_with(pat)
    }

    /// Advance the offset to the next unicode character.
    /// Returns `None` if file is at EOF.
    fn consume_char(&self) -> Option<char> {
        let c = self.peek_char();
        self.increment_byte_offsets(1);
        while !self.source.is_char_boundary(self.byte_offset.get()) {
            self.increment_byte_offsets(1);
        }
        if c == Some('\n') {
            self.next_line();
        }
        return c;
    }

    fn consume_lparen(&'a self, whitespace: &'a str) -> Token<'a> {
        let start = self.byte_offset.get();
        let line_offset = self.byte_offset_line.get();
        assert_eq!('(', self.consume_char().expect("consumed token at eof"));
        let value: &str = &self.source[start..self.byte_offset.get()];
        let site: Site = self.site(start, line_offset);
        Token::new(tokens::Kind::LParen, value, whitespace, site)
    }

    fn consume_rparen(&'a self, whitespace: &'a str) -> Token<'a> {
        let start = self.byte_offset.get();
        let line_offset = self.byte_offset_line.get();
        assert_eq!(')', self.consume_char().expect("consumed token at eof"));
        let value: &str = &self.source[start..self.byte_offset.get()];
        let site: Site = self.site(start, line_offset);
        Token::new(tokens::Kind::RParen, value, whitespace, site)
    }

    fn consume_number(&'a self, whitespace: &'a str) -> Token<'a> {
        let start = self.byte_offset.get();
        let line_offset = self.byte_offset_line.get();
        let value: &str = self.consume_identifier_string();
        let site: Site = self.site(start, line_offset);
        Token::new(tokens::Kind::Number, value, whitespace, site)
    }

    /// Consume characters as long as they can be part of the identifier.
    /// **Note:** backslashes are escaped and consume literally any
    /// character after them, regardless of 'kind', including whitespace.
    fn consume_identifier_string(&'a self) -> &'a str {
        let start = self.byte_offset.get();
        while let Some(c) = self.peek_char() {
            let Some(kind) = character_kind(c) else { break };
            // Symbols can contain escaped characters.
            if c == '\\' {
                let   _ = self.consume_char(); // `\`.
                let esc = self.consume_char(); // escaped char.
                if esc == Some('\n') {
                    self.next_line(); // NOTE: Disallow this?
                }
                continue;
            }
            // Characters that fit in a symbol or number are valid idents.
            match kind {
                tokens::Kind::Symbol
              | tokens::Kind::Number
              | tokens::Kind::Keyword => {},
                _ => break
            }
            let _ = self.consume_char();
        }
        &self.source[start..self.byte_offset.get()]
    }

    /// Consume a symbol/identifier token.
    fn consume_symbol(&'a self, whitespace: &'a str) -> Token<'a> {
        let start = self.byte_offset.get();
        let line_offset = self.byte_offset_line.get();
        let value: &str = self.consume_identifier_string();
        let site: Site = self.site(start, line_offset);
        Token::new(tokens::Kind::Symbol, value, whitespace, site)
    }

    /// A string is consumed as a token, but not parsed.
    fn consume_string(&'a self, whitespace: &'a str) -> Result<Token<'a>, LexError<'a>> {
        let start = self.byte_offset.get();
        let line_no = self.line.get();
        let line_offset = self.byte_offset_line.get();
        assert_eq!('"', self.peek_char().expect("consumed token at eof"));

        let token = if self.starts_with(r#"""""#) {
            // Tripple-quoted string.
            self.increment_byte_offsets(3);
            let start_of_string = self.byte_offset.get();
            // Read until end-of-string.
            let mut reading_escape = false;
            loop {
                let Some(next_char) = self.peek_char() else {
                    let site = Site::new(&self.source_path, &self.source, line_no, start, line_offset, 3);
                    return Err(LexError(
                        String::from("Unclosed tripple-quoted string."),
                        site));
                };
                if next_char == '\n' { self.next_line(); }
                if self.starts_with(r#"""""#) && !reading_escape {
                    break;  // End-of-string.
                }
                if !reading_escape {
                    reading_escape = next_char == '\\';
                } else {
                    reading_escape = false;
                }
                self.increment_byte_offsets(1);
            }
            let end_of_string = self.byte_offset.get();
            self.increment_byte_offsets(3);
            // String 'value' is inside quotes.
            let value: &str = &self.source[start_of_string..end_of_string];
            let mut site: Site = self.site(start, line_offset);
            site.line = line_no;
            Token::new(tokens::Kind::String, value, whitespace, site)
        } else {
            // Single-quoted string.
            self.increment_byte_offsets(1);
            let start_of_string = self.byte_offset.get();
            // Read until end-of-string.
            let mut reading_escape = false;
            loop {
                let Some(next_char) = self.peek_char() else {
                    let site = Site::new(&self.source_path, &self.source, line_no, start, line_offset, 1);
                    return Err(LexError(
                        String::from("Unclosed string quote (`\"')."),
                        site));
                };
                if next_char == '\n' { self.next_line(); }
                if next_char == '"' && !reading_escape {
                    break;  // End-of-string.
                }
                if !reading_escape {
                    reading_escape = next_char == '\\';
                } else {
                    reading_escape = false;
                }
                self.increment_byte_offsets(1);
            }
            let end_of_string = self.byte_offset.get();
            self.increment_byte_offsets(1);
            // String 'value' is inside quotes.
            let value: &str = &self.source[start_of_string..end_of_string];
            let mut site: Site = self.site(start, line_offset);
            site.line = line_no;
            Token::new(tokens::Kind::String, value, whitespace, site)
        };

        Ok(token)
    }

    fn consume_keyword(&'a self, whitespace: &'a str) -> Token<'a> {
        assert_eq!(':', self.consume_char().expect("consumed token at eof"));
        let start = self.byte_offset.get();  // Leave colon out of token value.
        let start_from_line = self.byte_offset_line.get();
        let value: &str = self.consume_identifier_string();
        let site: Site = self.site(start - 1, start_from_line  - 1);
        Token::new(tokens::Kind::Keyword, value, whitespace, site)
    }

    /// Generate site from start byte-index.
    fn site(&self, file_offset: usize, line_offset: usize) -> Site {
        let span = self.byte_offset.get() - file_offset;
        Site::new(&self.source_path, &self.source, self.line.get(), file_offset, line_offset, span)
    }

    pub fn consume(&'a self) -> Result<Token<'a>, LexError<'a>> {
        // Swallow up leading whitespace.
        let whitespace = self.consume_whitespace();
        // If there is any text left, continuie depending on the inital char.
        let character = self.peek_char().expect("tried to consume token on eof.");
        let token = match character_kind(character) {
            Some(tokens::Kind::LParen) => self.consume_lparen(whitespace),
            Some(tokens::Kind::RParen) => self.consume_rparen(whitespace),
            Some(tokens::Kind::Number) => self.consume_number(whitespace),
            Some(tokens::Kind::String) => self.consume_string(whitespace)?,
            Some(tokens::Kind::Symbol) => self.consume_symbol(whitespace),
            Some(tokens::Kind::Keyword) => self.consume_keyword(whitespace),
            None => unreachable!("incompletely consumed whitespace.")
        };
        Ok(token)
    }

    /// Perform an action that potentially advances us through
    /// the source-code, but restore to the lexer-state before said
    /// action (after getting its result), e.g. peeking tokens.
    pub fn restore<F, T>(&'a self, action: F) -> T
        where F: FnOnce(&'a Self) -> T
    {
        // Remeber current position in source code.
        let bo = self.byte_offset.get();
        let bol = self.byte_offset_line.get();
        let l = self.line.get();
        // Do some action, advancing the position.
        let ret = action(self);
        // Reset position to before doing the action.
        self.byte_offset.set(bo);
        self.byte_offset_line.set(bol);
        self.line.set(l);
        // What did the action produce.
        ret
    }

    /// Look ahead to the next token without advancing the
    /// source-code past it.
    pub fn peek(&'a self) -> Result<Token<'a>, LexError<'a>> {
        self.restore(|this: &'a Self| {
            this.consume()
        })
    }

    /// Check if file is at end-of-file.
    pub fn eof(&self) -> bool {
        self.restore(|this: &Self| {
            let _ = this.consume_whitespace();
            self.peek_char().is_none()
        })
    }
}
