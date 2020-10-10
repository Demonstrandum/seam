pub mod tokens;

pub mod lexer;

pub mod parser;

pub use parser::ParseTree;
use std::{fs, path::Path, io, error::Error};

pub fn parse_stream(stream : &mut impl io::Read) -> Result<ParseTree, Box<dyn Error>> {
    let mut contents = String::new();
    stream.read_to_string(&mut contents)?;
    let tokens = lexer::lex(contents, Option::<&Path>::None)?;
    let tree = parser::parse_stream(tokens)?;
    Ok(tree)
}

pub fn parse_file(path : &Path) -> Result<ParseTree, Box<dyn Error>> {
    let contents = fs::read_to_string(&path)?;
    let tokens = lexer::lex(contents, Some(path))?;
    let tree = parser::parse_stream(tokens)?;
    Ok(tree)
}

pub mod expander;
