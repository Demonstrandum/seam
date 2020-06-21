//! Assembles an expanded tree into valid HTML.
use super::Documentise;
use crate::parse::parser::{ParseNode, ParseTree};

use std::fmt::{self, Display};

#[derive(Debug, Clone)]
pub struct HTMLFormatter {
    pub tree : ParseTree
}

impl HTMLFormatter {
    pub fn new(tree : ParseTree) -> Self {
        Self { tree }
    }
}

pub const DEFAULT : &str =
    "<!DOCTYPE>\n\
    <html>\n\
        <head></head>\n\
        <body></body>\n\
    </html>";

impl Documentise for HTMLFormatter {
    fn document(&self) -> String {
        // Check if <!DOCTYPE html> exists.
        let mut doc = String::new();
        if self.tree.is_empty() {
            return String::from(DEFAULT);
        }
        let mut current_node = &self.tree[0];
        let mut has_declaration = false;

        if let ParseNode::List(list) = &current_node {
            if let Some(ParseNode::Symbol(declaration)) = &list.get(0) {
                if declaration.value.to_lowercase() == "!doctype" {
                    has_declaration = true;
                }
            }
        }

        if has_declaration {
            current_node = &self.tree[1];
        } else {
            doc += "<!DOCTYPE html>"
        }
        // Check if <html></html> root object exists.
        // Check if head exits, if not, make an empty one.
        // Check if body exists, if not, make it, and put everything
        // in there.

        doc += &self.to_string();

        doc
    }
}


// TODO: Convert special characters to HTML compatible ones.
// e.g.
//      <  =>  &lt;
//      >  =>  &gt;
//      &  =>  &amp;
//      "  =>  &quot;
//      !  =>  &excl;
//      etc.

/// Converting the tree to an HTML string.
impl Display for HTMLFormatter {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        for node in &self.tree {
            match node {
                ParseNode::Symbol(node) => write!(f, " {}", node.value)?,
                ParseNode::Number(node) => write!(f, " {}", node.value)?,
                ParseNode::String(node) => write!(f, " {}", node.value)?,
                ParseNode::List(list) => {
                    let head = list.first();
                    let mut tag = "";
                    if let Some(head_node) = head {
                        if let ParseNode::Symbol(head_symbol) = head_node {
                            tag = &head_symbol.value;
                            write!(f, "<{}", tag)?;
                        } else {
                            // Error, tags can only have symbol values.
                        }
                    } else {
                        // Error, empty tags not supported.
                    }

                    let mut rest = &list[1..];

                    // Declarations behave differently.
                    if tag.as_bytes()[0] == '!' as u8 {
                        // TODO: Following can only be symbols.
                        while !rest.is_empty() {
                            write!(f, " {}", rest[0])?;
                            rest = &rest[1..];
                        }
                        write!(f, ">")?;
                        continue;
                    }

                    while let Some(ParseNode::Attribute(attr)) = rest.first() {
                        if let Some(atom) = (*attr.node).atomic() {
                            write!(f, " {}=\"{}\"", attr.keyword, atom.value)?;
                            rest = &rest[1..];
                        } else {
                            // Error! Cannot be non atomic.
                        }
                    }
                    writeln!(f, ">")?;

                    let html_fmt = HTMLFormatter::new(rest.to_owned());
                    writeln!(f, "{}", html_fmt)?;
                    write!(f, "</{}>", tag)?;
                },
                _ => write!(f, "hi")?,
            }
        }
        write!(f, "")
    }
}
