#![allow(incomplete_features)]
#![feature(pattern)]
#![feature(associated_type_defaults)]

pub mod parse;
pub mod assemble;

use parse::{expander, parser, lexer};

use std::{fs, io, path::Path};

pub const VERSION: (u8, u8, u8) = (0, 3, 0);

pub fn tree_builder<'a, P: AsRef<Path>>(source_path: Option<P>, string: String)
    -> expander::Expander<'a> {
    let path = source_path.map_or("<stdin>".to_string(),
        |s| s.as_ref().to_string_lossy().to_string());
    let tokenizer = lexer::Lexer::new(path, string);
    let builder = parser::Parser::new(tokenizer);
    expander::Expander::new(builder)
}

pub fn tree_builder_file<'a>(path: &Path)
    -> io::Result<expander::Expander<'a>> {
    let contents = fs::read_to_string(&path)?;
    Ok(tree_builder(Some(path), contents))
}

pub fn tree_builder_stream(stream: &mut impl io::Read)
    -> io::Result<expander::Expander> {
    let mut contents = String::new();
    stream.read_to_string(&mut contents)?;
    Ok(tree_builder(Option::<&Path>::None, contents))
}

pub fn main() {
    eprintln!("Library main function should not be used.");
    std::process::exit(1);
}
