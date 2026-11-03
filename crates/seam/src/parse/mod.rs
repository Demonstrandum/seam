pub mod tokens;
pub mod lexer;
pub mod parser;
#[macro_use]
pub mod macros;
pub mod expander;

pub use parser::ParseTree;
use std::{fs, path::Path, error::Error};

/// Build a parser for a file without expanding macros.
/// When `literate`, the file is plain text with embedded `(%...)` macro calls.
pub fn parser_for_file(path: &Path, literate: bool) -> Result<parser::Parser, Box<dyn Error>> {
    let contents = fs::read_to_string(path)?;
    let tokenizer = lexer::Lexer::new(path.to_string_lossy().to_string(), contents);
    Ok(if literate { parser::Parser::literate(tokenizer) } else { parser::Parser::new(tokenizer) })
}
