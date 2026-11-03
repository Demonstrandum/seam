use std::{borrow::Cow, fmt::{self, Display}, hash::{DefaultHasher, Hash, Hasher}};
use unicode_width::UnicodeWidthStr;

/// A source file: its path (or some other name) and its contents.
#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: Cow<'static, str>,
    pub code: Cow<'static, str>,
}

const UNKNOWN_FILE: SourceFile = SourceFile {
    path: Cow::Borrowed("<unknown>"),
    code: Cow::Borrowed(""),
};

/// Precise source-code location a parsed (or lexed) node (or token).
/// Including a reference to the source file, line number, bytes offsets
/// within the file, including from start of line, and the number of
/// bytes it occupies in the source.
/// Offsets are 32-bit, to keep every node small.
#[derive(Debug, Clone, Copy)]
pub struct Site<'a> {
    pub file: &'a SourceFile,
    pub line: u32,
    pub bytes_from_start: u32,
    pub bytes_from_start_of_line: u32,
    pub bytes_span: u32,
}

/// Dummy (unknown) site.
pub const UNKNOWN_SITE: Site<'static> = Site {
    file: &UNKNOWN_FILE,
    line: 0,
    bytes_from_start: 0,
    bytes_from_start_of_line: 0,
    bytes_span: 0,
};

/// Convert a byte offset or line number to 32-bits.
fn narrow(n: usize) -> u32 {
    u32::try_from(n).unwrap_or(u32::MAX)
}

impl<'a> Site<'a> {
    #[must_use]
    pub fn new(file: &'a SourceFile,
               line: usize,
               bytes_from_start: usize,
               bytes_from_start_of_line: usize,
               bytes_span: usize) -> Self {
        Self {
            file,
            line: narrow(line),
            bytes_from_start: narrow(bytes_from_start),
            bytes_from_start_of_line: narrow(bytes_from_start_of_line),
            bytes_span: narrow(bytes_span),
        }
    }

    /// The same site, but starting on the given line
    /// (e.g. for a token spanning several lines).
    #[must_use]
    pub fn starting_on(mut self, line: usize) -> Self {
        self.line = narrow(line);
        self
    }

    /// Path (or name) of the source file.
    #[must_use]
    pub fn source(&self) -> &'a str {
        &self.file.path
    }

    /// Contents of the source file.
    #[must_use]
    pub fn source_code(&self) -> &'a str {
        &self.file.code
    }

    /// Byte-offset in source code where this site starts.
    #[must_use]
    pub fn start(&self) -> usize {
        self.bytes_from_start as usize
    }

    /// Byte-offset in source code where this site ends.
    #[must_use]
    pub fn end(&self) -> usize {
        (self.bytes_from_start + self.bytes_span) as usize
    }

    #[must_use]
    pub fn uuid(&self) -> String {
        let mut hasher = DefaultHasher::new();
        self.hash(&mut hasher);
        let hash = hasher.finish();
        format!("{}-{}", hash, self.bytes_from_start)
    }

    #[must_use]
    pub const fn unknown() -> Self { UNKNOWN_SITE }

    /// Byte-offset in source code for start-of-line where this site is.
    #[must_use]
    pub fn start_of_line(&self) -> usize {
        (self.bytes_from_start - self.bytes_from_start_of_line) as usize
    }

    /// Find byte-offset in source code of end-of-line where this site is.
    #[must_use]
    pub fn end_of_line(&self) -> usize {
        let code = self.source_code();
        let mut i = self.start();
        let bytes = code.as_bytes();
        while i < code.len() {
            if bytes[i] == b'\n' {
                return i;
            }
            i += 1;
        }
        i
    }

    /// Get a string slice into the part of the source-code
    /// which occupies the location this site references.
    #[must_use]
    pub fn view(&self) -> &'a str {
        &self.source_code()[self.start()..self.end()]
    }

    /// Get string view into whole line that this site is referencing.
    #[must_use]
    pub fn line_slice(&self) -> &'a str {
        &self.source_code()[self.start_of_line()..self.end_of_line()]
    }

    /// Compute (monospace, terminal) column width of piece of text
    /// referenced by this site in the source code.
    #[must_use]
    pub fn width(&self) -> usize {
        UnicodeWidthStr::width(self.view())
    }

    /// Compute which column the site starts at on the line,
    /// accounting for the rendered number of columns for each character
    /// in a terminal, according to the same procedure as [`Self::width`].
    #[must_use]
    pub fn line_column(&self) -> usize {
        let preceeding = &self.source_code()[self.start_of_line()..self.start()];
        UnicodeWidthStr::width(preceeding) + 1
    }
}

impl Hash for Site<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.source().hash(state);
        self.line.hash(state);
        self.bytes_from_start.hash(state);
        self.bytes_from_start_of_line.hash(state);
        self.bytes_span.hash(state);
    }
}

impl Display for Site<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        write!(f, "{}:", self.source())?;
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

#[derive(Debug, Clone, Copy)]
pub struct Token<'a> {
    pub kind: Kind,
    pub value: &'a str,
    pub leading_whitespace: &'a str,
    pub site: Site<'a>,
}

impl<'a> Token<'a> {
    #[must_use]
    pub fn new(kind: Kind, value: &'a str, leading_whitespace: &'a str, site: Site<'a>) -> Self {
        Self { kind, value, leading_whitespace, site }
    }
}
