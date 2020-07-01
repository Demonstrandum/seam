use crate::parse::tokens::Site;
use std::{convert, fmt, error::Error};

use colored::*;

/// Error type for specific errors with generating
/// each type of markup.
#[derive(Debug, Clone)]
pub struct GenerationError {
    pub markup : String,
    pub message : String,
    pub site : Site
}

impl GenerationError {
    /// Create a new error given the ML, the message, and the site.
    pub fn new(ml : &str, msg : &str, site : &Site) -> Self {
        Self {
            markup: ml.to_owned(),
            message: msg.to_owned(),
            site: site.to_owned()
        }
    }
    /// When an error cannot be given a location,
    /// or exact point of failure.
    pub fn unknown(ml : &str) -> Self {
        Self {
            markup: ml.to_owned(),
            message: String::from("Unknown generation error (bug)."),
            site: Site::fake()
        }
    }
}

/// Implement fmt::Display for user-facing error output.
impl fmt::Display for GenerationError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}",
            format!("[{}] Error Generating {} {}",
                "**".red().bold(),
                self.markup.bold(), self.site).white(),
            self.message)
    }
}

/// Implements std::error::Error.
impl Error for GenerationError { }

/// An fmt::Error can be cast to an equally horribly
/// ambiguous GenerationError.
impl convert::From<fmt::Error> for GenerationError {
    fn from(_ : fmt::Error) -> Self {
        Self {
            markup: String::from("Unknown"),
            message: String::from(
                "Unknown error while writing to format buffer"),
            site: Site::fake()
        }
    }
}

/// Trait for all structs that can generate specific markup
/// for the s-expression tree.
pub trait MarkupDisplay {
    // Required definitions:
    /// Similar to fmt in Display/Debug traits, takes in a
    /// mutable writable buffer, returns success or a specifc
    /// error while generating the markup.
    fn generate(&self, buf : &mut dyn fmt::Write)
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
        let mut s_buf = String::new();
        self.generate(&mut s_buf).map(|_| s_buf)
    }
}

/// Automatically implement fmt::Display as a wrapper around
/// MarkupDisplay::generate, but throws away the useful error message.
impl fmt::Display for dyn MarkupDisplay {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        self.generate(f).map_err(|_| fmt::Error)
    }
}
/// XML generation.
pub mod xml;

/// HTML5 CSS generation.
pub mod css;
/// HTML5 HTML generation.
pub mod html;

