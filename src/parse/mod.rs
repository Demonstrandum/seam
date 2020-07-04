pub mod tokens;

pub mod lexer;

pub mod parser;

use parser::ParseTree;
use std::{fs, path::Path, error::Error};

pub fn parse_file(path : &Path) -> Result<ParseTree, Box<dyn Error>> {
    let contents = fs::read_to_string(&path)?;
    let tokens = lexer::lex(contents, Some(path))?;
    let tree = parser::parse_stream(tokens)?;
    Ok(tree)
}

pub mod expander;
