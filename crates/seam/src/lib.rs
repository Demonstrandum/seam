#![allow(incomplete_features)]
#![feature(pattern)]
#![feature(box_patterns)]
#![feature(associated_type_defaults)]

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

/* Utilities. */

/// See: <https://stackoverflow.com/a/30353928>
pub trait CloneBox {
    fn clone_box(&self) -> *mut ();
}

impl<'a, T> CloneBox for T where T: Clone + 'a {
    fn clone_box(&self) -> *mut () {
        Box::<T>::into_raw(Box::new(self.clone())) as *mut ()
    }
}

#[macro_export]
macro_rules! impl_clone_box {
    ($($lif:tt),* ; $tra:ty) => {
        impl< $($lif),* > Clone for Box< $tra > {
            fn clone(&self) -> Box< $tra > {
                unsafe {
                    *Box::from_raw(self.clone_box() as *mut Self)
                }
            }
        }
    };
    ($($lif:tt),* ; $($gen:tt),* ; $tra:ty) => {
        impl< $($lif),* , $($gen),* > Clone for Box< $tra > {
            fn clone(&self) -> Box< $tra > {
                unsafe {
                    *Box::from_raw(self.clone_box() as *mut Self)
                }
            }
        }
    };
}

/* Library helpers. */

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

#[cfg(test)]
#[path = "./tests.rs"]
mod tests;
