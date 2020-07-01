//! Assembles an expanded tree into valid CSS.
use super::{GenerationError, MarkupDisplay};
use crate::parse::parser::{self, ParseNode, ParseTree};

use std::fmt;

#[derive(Debug, Clone)]
pub struct CSSFormatter {
    pub tree : ParseTree,
}

impl CSSFormatter {
    pub fn new(tree : ParseTree) -> Self {
        Self { tree }
    }
}

pub const DEFAULT : &str = "\n";

/// Function responsible for translating a CSS value (i.e.
/// a value of a CSS property) from some s-expression into
/// a valid CSS value.
pub fn css_value(property : &str, node : &ParseNode) -> String {
    String::from("x")
}

impl MarkupDisplay for CSSFormatter {
    fn document(&self) -> Result<String, GenerationError> {
        let mut doc = String::new();
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }
        self.generate(&mut doc)?;
        Ok(doc)
    }

    fn generate(&self, f : &mut dyn fmt::Write)
    -> Result<(), GenerationError> {
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            match node {
                ParseNode::List(list) => {
                    let stripped = parser::strip(list, false);
                    let iter = stripped.iter();
                    let mut prop_i = 0; // Index of first property.
                    let mut selectors = iter.clone()
                        .take_while(|n| { prop_i += 1; n.atomic().is_some() })
                        .map(|n| n.atomic().unwrap()) // We've checked.
                        .peekable();

                    // Check we were actually provided with
                    // some selectors.
                    if selectors.peek().is_none() {
                        return Err(GenerationError::new("CSS",
                            "CSS selector(s) missing. \
                             Expected a symbol node, none was found!",
                             &node.site()));
                    }
                    // Join the selectors togeher.
                    for selector in selectors {
                        write!(f, "{} ", selector.value)?;
                    }
                    writeln!(f, "{{")?;

                    let properties = iter.skip(prop_i - 1);

                    for property in properties {
                        if let ParseNode::Attribute(property) = property {
                            let value = &property.node;
                            writeln!(f, "  {}: {};",
                                     &property.keyword,
                                     css_value(&property.keyword, value))?;
                        } else {
                            return Err(GenerationError::new("CSS",
                                "CSS property-value pairs must be in the \
                                 form of attributes, i.e. `:property value`.",
                                 &property.site()));
                        }
                    }
                    writeln!(f, "}}\n")?;

                },
                ParseNode::Attribute(attr) => {
                    let site = attr.site.to_owned();
                    return Err(GenerationError::new("CSS",
                        "Attribute not expected here, CSS documents \
                         are supposed to be a series of selectors \
                         and property-value pairs, wrapped in parentheses.",
                         &site));
                },
                ParseNode::Symbol(node)
                | ParseNode::Number(node)
                | ParseNode::String(node) => {
                    let site = node.site.to_owned();
                    if node.value.trim().is_empty() {
                        continue;
                    }
                    return Err(GenerationError::new("CSS",
                        "Symbolic node not expected here, CSS documents \
                         are supposed to be a series of selectors \
                         and property-value pairs, wrapped in parentheses.",
                         &site));
                }
            }
        }
        Ok(())
    }
}

