use crate::parse::tokens::Site;
use std::{convert, fmt, error::Error};

use colored::*;

#[derive(Debug, Clone)]
pub struct GenerationError {
    pub markup : String,
    pub message : String,
    pub site : Site
}

impl GenerationError {
    pub fn new(ml : &str, msg : &str, site : &Site) -> Self {
        Self {
            markup: ml.to_owned(),
            message: msg.to_owned(),
            site: site.to_owned()
        }
    }
    pub fn unknown(ml : &str) -> Self {
        Self {
            markup: ml.to_owned(),
            message: String::from("Unknown generation error (bug)."),
            site: Site::fake()
        }
    }
}

impl fmt::Display for GenerationError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}",
            format!("[{}] Error Generating {} {}",
                "**".red().bold(),
                self.markup.bold(), self.site).white(),
            self.message)
    }
}

impl Error for GenerationError { }

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

pub trait MarkupDisplay {
    // Required definitions:
    fn generate(&self, buf : &mut dyn fmt::Write)
        -> Result<(), GenerationError>;
    fn document(&self) -> Result<String, GenerationError>;
    // Default definitions:
    fn display(&self) -> Result<String, GenerationError> {
        let mut s_buf = String::new();
        self.generate(&mut s_buf).map(|_| s_buf)
    }
}

impl fmt::Display for dyn MarkupDisplay {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        self.generate(f).map_err(|_| fmt::Error)
    }
}
/// XML generation.
pub mod xml;

/// HTML5 CSS generation.
//pub mod css;
/// HTML5 HTML generation.
pub mod html;

