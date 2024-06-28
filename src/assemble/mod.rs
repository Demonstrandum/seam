use crate::parse::tokens::Site;
use std::{convert, fmt, error::Error};

use colored::*;
use unicode_width::UnicodeWidthStr;

/// Error type for specific errors with generating
/// each type of markup.
#[derive(Debug, Clone)]
pub struct GenerationError<'a> {
    pub markup: String,
    pub message: String,
    pub site: Site<'a>,
}

impl<'a> GenerationError<'a> {
    /// Create a new error given the ML, the message, and the site.
    pub fn new(ml: &str, msg: &str, site: &Site<'a>) -> Self {
        Self {
            markup: ml.to_owned(),
            message: msg.to_owned(),
            site: site.to_owned(),
        }
    }
}

/// Implement fmt::Display for user-facing error output.
impl<'a> fmt::Display for GenerationError<'a> {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        let line_prefix = format!("  {} |", self.site.line);
        let line_view = self.site.line_slice();
        writeln!(f, "{} {}", line_prefix, line_view)?;
        writeln!(f, "{:>prefix_offset$} {:~>text_offset$}{:^>length$}", "|", "", "",
            prefix_offset=UnicodeWidthStr::width(line_prefix.as_str()),
            text_offset=self.site.line_column() - 1,
            length=self.site.width())?;
        write!(f, "{}: {}",
            format!("[{}] Error Generating {} ({}:{}:{})",
                "**".red().bold(),
                self.markup.bold(),
                self.site.source,
                self.site.line,
                self.site.line_column(),
            ).black(),
            self.message)
    }
}

/// Implements std::error::Error.
impl<'a> Error for GenerationError<'a> { }

/// Convert from an io::Error to a generation error.
impl<'a> From<std::io::Error> for GenerationError<'a> {
    fn from(e: std::io::Error) -> Self {
        Self {
            markup: String::from("<markup>"), // FIXME.
            message: format!("IO error: {}", e),
            site: Site::unknown(),
        }
    }
}

/// An fmt::Error can be cast to an equally horribly
/// ambiguous GenerationError.
impl<'a> convert::From<fmt::Error> for GenerationError<'a> {
    fn from(e: fmt::Error) -> Self {
        Self {
            markup: String::from("<markup>"),
            message: format!("Format buffer error: {}", e),
            site: Site::unknown(),
        }
    }
}

pub type Formatter<'a> = &'a mut dyn fmt::Write;

/// Trait for all structs that can generate specific markup
/// for the s-expression tree.
pub trait MarkupDisplay {
    // Required definitions:
    /// Similar to fmt in Display/Debug traits, takes in a
    /// mutable writable buffer, returns success or a specifc
    /// error while generating the markup.
    fn generate(&self, buf : Formatter)
        -> Result<(), GenerationError>;
    /// Documentises the input, that's to say, it adds any
    /// extra meta-information to the generated markup, if
    /// the s-expressions your wrote ommited it.
    /// e.g. All XML gets a `<?xml ... ?>` tag added to it.
    fn document(&self) -> Result<String, GenerationError>;
    // Default definitions:
    /// Directly converts the s-expressions into a string
    /// containing the markup, unless there was an error.
    fn display(&self) -> Result<String, GenerationError> {
        let mut buf = String::new();
        self.generate(&mut buf)?;
        Ok(buf)
    }
}

/// Automatically implement fmt::Display as a wrapper around
/// MarkupDisplay::generate, but throws away the useful error message.
impl fmt::Display for dyn MarkupDisplay {
    fn fmt(&self, f : &mut fmt::Formatter) -> fmt::Result {
        self.generate(f).map_err(|_| fmt::Error)
    }
}

/// Parforms the following escapes:
/// - `<` → `&lt;`
/// - `>` → `&gt;`
/// - `"` → `&quot;`
/// - `'` → `&apos;`
/// - `&` → `&amp;`
pub fn escape_xml(string: &str) -> String {
    let mut bytes = string.bytes();
    let mut byte_builder: Vec<u8> = Vec::with_capacity(bytes.len());
    while let Some(byte) = bytes.next() {
        match byte {
            b'<'  => byte_builder.extend(b"&lt;"),
            b'>'  => byte_builder.extend(b"&gt;"),
            b'"'  => byte_builder.extend(b"&quot;"),
            b'\'' => byte_builder.extend(b"&apos;"),
            b'&'  => byte_builder.extend(b"&amp;"),
            _ => byte_builder.push(byte)
        }
    }
    unsafe {
        String::from_utf8_unchecked(byte_builder)
    }
}

/// Re-constitute original S-expressions.
pub mod sexp;
/// XML generation.
pub mod xml;
/// HTML5 CSS generation.
pub mod css;
/// HTML5 HTML generation.
pub mod html;
