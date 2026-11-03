#![allow(incomplete_features)]
#![feature(pattern)]

pub mod parse;
pub mod assemble;

use parse::{expander, parser, lexer};

use std::{fs, io, path::Path};

const fn parse_u8(s: &str) -> u8 {
    match u8::from_str_radix(s, 10) {
        Ok(n) => n,
        Err(_) => panic!("is not a base 10 integer"),
    }
}

pub const VERSION: (u8, u8, u8) = (
    parse_u8(env!("CARGO_PKG_VERSION_MAJOR")),
    parse_u8(env!("CARGO_PKG_VERSION_MINOR")),
    parse_u8(env!("CARGO_PKG_VERSION_PATCH")),
);

/* Library helpers. */

pub use expander::Context;

/// Build an expander for some source code.
/// When `literate`, the source is plain text with embedded `(%...)` macro calls.
pub fn tree_builder<'a, P: AsRef<Path>>(context: &'a Context<'a>, source_path: Option<P>, string: String, literate: bool)
    -> expander::Expander<'a> {
    let path = source_path.map_or("<stdin>".to_string(),
        |s| s.as_ref().to_string_lossy().to_string());
    let tokenizer = lexer::Lexer::new(path, string);
    let builder = if literate { parser::Parser::literate(tokenizer) } else { parser::Parser::new(tokenizer) };
    expander::Expander::new(context, builder)
}

pub fn tree_builder_file<'a>(context: &'a Context<'a>, path: &Path, literate: bool)
    -> io::Result<expander::Expander<'a>> {
    let contents = fs::read_to_string(path)?;
    Ok(tree_builder(context, Some(path), contents, literate))
}

pub fn tree_builder_stream<'a>(context: &'a Context<'a>, stream: &mut impl io::Read, literate: bool)
    -> io::Result<expander::Expander<'a>> {
    let mut contents = String::new();
    stream.read_to_string(&mut contents)?;
    Ok(tree_builder(context, Option::<&Path>::None, contents, literate))
}

#[cfg(test)]
#[path = "./tests.rs"]
mod tests;
