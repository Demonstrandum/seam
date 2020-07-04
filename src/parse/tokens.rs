use std::rc::Rc;
use std::fmt::{self, Display};

#[derive(Debug, Clone)]
pub struct Site {
    pub source : Option<Rc<str>>,
    pub line : usize,
    pub bytes_from_start : usize,
    pub bytes_span : usize,
}

impl Site {
    pub fn new(source : Rc<str>, line : usize,
            bytes_from_start : usize,
            bytes_span : usize) -> Self {
        Self {
            source: Some(source),
            line, bytes_from_start,
            bytes_span
        }
    }

    pub fn fake() -> Self {
        Self {
            source: None,
            line: 0,
            bytes_from_start: 0,
            bytes_span: 0
        }
    }

    pub fn from_line(line : usize,
                     bytes_from_start : usize,
                     bytes_span : usize) -> Self {
        Self {
            source: None,
            line, bytes_from_start,
            bytes_span
        }
    }
}

impl Display for Site {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        if let Some(source) = &self.source {
            write!(f, "{}:", source)?;
        } else {
            write!(f, "no-file:")?;
        }
        write!(f, "{}:{})", self.line, self.bytes_from_start + 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Kind {
    LParen,
    RParen,
    Symbol,
    String,
    Number,
    Keyword,
    Whitespace,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind : Kind,
    pub value : String,
    pub site : Site,
}

impl Token {
    pub fn new(kind : Kind, value : String, site : Site) -> Self {
        Self { kind, value, site }
    }
}

pub type TokenStream = Vec<Token>;
