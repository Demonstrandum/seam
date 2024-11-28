use std::fmt::{self, Display};
use unicode_width::UnicodeWidthStr;

/// Precise source-code location a parsed (or lexed) node (or token).
/// Including references to the source-code and path, line number, bytes offsets
/// within the file, including from start of line, and the number of
/// bytes it occupies in the source.
#[derive(Debug, Clone)]
pub struct Site<'a> {
    pub source: &'a str,
    pub source_code: &'a str,
    pub line: usize,
    pub bytes_from_start: usize,
    pub bytes_from_start_of_line: usize,
    pub bytes_span: usize,
}

/// Dummy (unknown) site.
pub const UNKNOWN_SITE: Site<'static> = Site {
    source: "<unknwon>",
    source_code: "",
    line: 0,
    bytes_from_start: 0,
    bytes_from_start_of_line: 0,
    bytes_span: 0,
};

impl<'a> Site<'a> {
    pub fn new(source: &'a str,
               source_code: &'a str,
               line: usize,
               bytes_from_start: usize,
               bytes_from_start_of_line: usize,
               bytes_span: usize) -> Self {
        Self {
            source,
            source_code,
            line,
            bytes_from_start,
            bytes_from_start_of_line,
            bytes_span,
        }
    }

    pub const fn unknown() -> Self { UNKNOWN_SITE }

    /// Byte-offset in source code for start-of-line where this site is.
    pub fn start_of_line(&self) -> usize {
        self.bytes_from_start - self.bytes_from_start_of_line
    }

    /// Find byte-offset in source code of end-of-line where this site is.
    pub fn end_of_line(&self) -> usize {
        let mut i = self.bytes_from_start;
        let bytes = self.source_code.as_bytes();
        while i < self.source_code.len() {
            if bytes[i] == '\n' as u8 {
                return i;
            }
            i += 1;
        }
        return i;
    }

    /// Get a string slice into the part of the source-code
    /// which occupies the location this site references.
    pub fn view(&'a self) -> &'a str {
        let start = self.bytes_from_start;
        let end = start + self.bytes_span;
        &self.source_code[start..end]
    }

    /// Get string view into whole line that this site is referencing.
    pub fn line_slice(&self) -> &'a str {
        &self.source_code[self.start_of_line()..self.end_of_line()]
    }

    /// Compute (monospace, terminal) column width of piece of text
    /// referenced by this site in the source code.
    pub fn width(&self) -> usize {
        let text = &self.source_code[self.bytes_from_start..self.bytes_from_start + self.bytes_span];
        UnicodeWidthStr::width(text)
    }

    /// Compute which column the site starts at on the line,
    /// accounting for the rendered number of columns for each character
    /// in a terminal, according to the same procedure as [`Self::width`].
    pub fn line_column(&self) -> usize {
        let preceeding = &self.source_code[self.start_of_line()..self.bytes_from_start];
        UnicodeWidthStr::width(preceeding) + 1
    }
}

impl<'a> Display for Site<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        write!(f, "{}:", self.source)?;
        write!(f, "{}:{}", self.line, self.line_column())?;
        write!(f, ")")
    }
}

/// Kinds of possible tokens.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Kind {
    LParen,
    RParen,
    Symbol,
    String,
    Number,
    Keyword,
}

#[derive(Debug, Clone)]
pub struct Token<'a> {
    pub kind: Kind,
    pub value: &'a str,
    pub leading_whitespace: &'a str,
    pub site: Site<'a>,
}

impl<'a> Token<'a> {
    pub fn new(kind: Kind, value: &'a str, leading_whitespace: &'a str, site: Site<'a>) -> Self {
        Self { kind, value, leading_whitespace, site }
    }
}
