use crate::parse::{parser::ParseNode, tokens::Site};
use std::{convert, error::Error, fmt::{self, Debug}};

use colored::Colorize;
use unicode_width::UnicodeWidthStr;

/// Error type for specific errors with generating
/// each type of markup.
#[derive(Debug, Clone)]
pub struct GenerationError<'a> {
    pub markup: &'static str,
    pub message: String,
    pub site: Site<'a>,
}

impl<'a> GenerationError<'a> {
    /// Create a new error given the ML, the message, and the site.
    #[must_use]
    pub fn new(ml: &'static str, msg: &str, site: &Site<'a>) -> Self {
        Self {
            markup: ml,
            message: msg.to_owned(),
            site: site.to_owned(),
        }
    }
}

/// Implement `fmt::Display` for user-facing error output.
impl fmt::Display for GenerationError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let line_prefix = format!("  {} |", self.site.line);
        let line_view = self.site.line_slice();
        writeln!(f)?;
        writeln!(f, "{line_prefix} {line_view}")?;
        writeln!(f, "{:>prefix_offset$} {:~>text_offset$}{:^>length$}", "|", "", "",
            prefix_offset=UnicodeWidthStr::width(line_prefix.as_str()),
            text_offset=self.site.line_column() - 1,
            length=self.site.width())?;
        writeln!(f, "{}: {}",
            format!("[{}] Error Generating {} ({}:{}:{})",
                "**".red().bold(),
                self.markup.bold(),
                self.site.source(),
                self.site.line,
                self.site.line_column(),
            ).black(),
            self.message)
    }
}

/// Implements `std::error::Error`.
impl Error for GenerationError<'_> { }

/// Convert from an `io::Error` to a generation error.
impl From<std::io::Error> for GenerationError<'_> {
    fn from(e: std::io::Error) -> Self {
        Self {
            markup: "<markup>",
            message: format!("IO error: {e}"),
            site: Site::unknown(),
        }
    }
}

/// An `fmt::Error` can be cast to an equally horribly
/// ambiguous `GenerationError`.
impl convert::From<fmt::Error> for GenerationError<'_> {
    fn from(e: fmt::Error) -> Self {
        Self {
            markup: "<markup>",
            message: format!("Format buffer error: {e}"),
            site: Site::unknown(),
        }
    }
}

pub type Formatter<'a> = &'a mut dyn fmt::Write;

/// Leading whitespace to write before the `index`th child of an element:
/// the first child's whitespace is left out, unless it starts on a new line.
/// e.g. `(p hello world)` -> `<p>hello world</p>`.
#[must_use]
pub fn child_whitespace<'n>(index: usize, node: &'n ParseNode) -> &'n str {
    let leading = node.leading_whitespace();
    if index == 0 && !leading.contains('\n') { "" } else { leading }
}

/// Trait for all structs that can generate specific markup
/// for the s-expression tree.
pub trait MarkupFormatter<'a>: Debug {
    // Required definitions:
    /// Similar to fmt in Display/Debug traits, takes in a
    /// mutable writable buffer, returns success or a specifc
    /// error while generating the markup.
    fn generate(&self, buf: Formatter) -> Result<(), GenerationError<'a>>;
    /// Documentises the input, that's to say, it adds any
    /// extra meta-information to the generated markup, if
    /// the s-expressions your wrote ommited it.
    /// e.g. All XML gets a `<?xml ... ?>` tag added to it.
    fn document(&self) -> Result<String, GenerationError<'a>>;
    // Default definitions:
    /// Directly converts the s-expressions into a string
    /// containing the markup, unless there was an error.
    fn display(&self) -> Result<String, GenerationError<'a>> {
        let mut buf = String::new();
        self.generate(&mut buf)?;
        Ok(buf)
    }
}

/// Automatically implement `fmt::Display` as a wrapper around
/// `MarkupFormatter::generate`, but throws away the useful error message.
impl fmt::Display for dyn MarkupFormatter<'_> + '_ {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.generate(f).map_err(|_| fmt::Error)
    }
}

/// Write `text` with the following escapes:
/// - `<` → `&lt;`
/// - `>` → `&gt;`
/// - `"` → `&quot;`
/// - `'` → `&apos;`
/// - `&` → `&amp;`
pub fn write_escaped(f: &mut dyn fmt::Write, text: &str) -> fmt::Result {
    let mut written = 0;
    for (index, byte) in text.bytes().enumerate() {
        let escape = match byte {
            b'<'  => "&lt;",
            b'>'  => "&gt;",
            b'"'  => "&quot;",
            b'\'' => "&apos;",
            b'&'  => "&amp;",
            _ => continue,
        };
        f.write_str(&text[written..index])?;
        f.write_str(escape)?;
        written = index + 1;
    }
    f.write_str(&text[written..])
}

/// Escape a string (see [`write_escaped`]).
#[must_use]
pub fn escape_xml(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    // Writing to a `String` never fails.
    let _ = write_escaped(&mut escaped, text);
    escaped
}

/// A writer which escapes everything written through it (see [`write_escaped`]).
pub struct Escaping<'f>(pub &'f mut dyn fmt::Write);

impl fmt::Write for Escaping<'_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        write_escaped(self.0, text)
    }
}

/// Re-constitute original S-expressions.
pub mod sexp;
/// Converts source into expanded plain-text.
pub mod text;
/// XML generation.
pub mod xml;
/// HTML5 CSS generation.
pub mod css;
/// HTML5 HTML generation.
pub mod html;
