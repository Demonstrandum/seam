pub mod parse;
pub mod assemble;

use parse::{expander, parser, lexer};

use std::error::Error;
use std::{fs, path::Path};

pub const VERSION : (u8, u8, u8) = (0, 1, 0);

pub fn parse<P: AsRef<Path>>(string : String, source : Option<P>)
    -> Result<parser::ParseTree, Box<dyn Error>> {
    let tokens = lexer::lex(string, source)?;
    #[cfg(feature="debug")]
    eprintln!("{:#?}", &tokens);
    let tree = parser::parse_stream(tokens)?;
    let expanded = expander::expand(tree)?;
    Ok(expanded)
}

pub fn parse_file(path : &Path)
    -> Result<parser::ParseTree, Box<dyn Error>> {
    let contents = fs::read_to_string(&path)?;
    parse(contents, Some(&path))
}

pub fn main() {
    eprintln!("Library main function should not be used.");
    std::process::exit(1);
}
