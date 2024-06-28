pub mod tokens;
pub mod lexer;
pub mod parser;
pub mod expander;

pub use parser::ParseTree;
use std::{fs, path::Path, error::Error};

/// Build a parser for a file without expanding macros.
pub fn parser_for_file(path: &Path) -> Result<parser::Parser, Box<dyn Error>> {
    let contents = fs::read_to_string(&path)?;
    let tokenizer = lexer::Lexer::new(path.to_string_lossy().to_string(), contents);
    let builder = parser::Parser::new(tokenizer);
    Ok(builder)
}
