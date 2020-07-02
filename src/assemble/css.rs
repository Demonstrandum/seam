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

/// All CSS functions, I might have missed a few.
const CSS_FUNCTIONS : [&str; 52] = [
    "attr", "blur", "brightness", "calc", "circle", "contrast",
    "counter", "counters", "cubic-bezier", "drop-shadow", "ellipse",
    "grayscale", "hsl", "hsla", "hue-rotate", "hwb", "image", "inset",
    "invert", "linear-gradient", "matrix", "matrix3d", "opacity",
    "perspective", "polygon", "radial-gradient", "repeating-linear-gradient",
    "repeating-radial-gradient", "rgb", "rgba", "rotate", "rotate3d",
    "rotateX", "rotateY", "rotateZ", "saturate", "sepia", "scale", "scale3d",
    "scaleX", "scaleY", "scaleZ", "skew", "skewX", "skewY", "symbols",
    "translate", "translate3d", "translateX", "translateY", "translateZ",
    "url",
];

/// The only four math operations supported by CSS calc(...),
/// or at least I think.
const BINARY_OPERATORS : [&str; 4] = ["+", "-", "*", "/"];

fn convert_value(node : &ParseNode) -> Result<String, GenerationError> {
    match node {
        ParseNode::List(list) => {
            let list = parser::strip(list, false);
            let result = match list.as_slice() {
                [head, tail@..] => {
                    let head = convert_value(head)?;

                    let mut tail_tmp = vec![String::new(); tail.len()];
                    for (i, e) in tail.iter().enumerate() {
                        tail_tmp[i] = convert_value(e)?
                    }
                    let tail = tail_tmp.as_slice();

                    let args = tail.iter()
                        .fold(String::new(), |acc, s| acc + " " + &s);
                    let args = args.trim();
                    if CSS_FUNCTIONS.contains(&head.as_str()) {
                        format!("{}({})", head, args)
                    } else if BINARY_OPERATORS.contains(&head.as_str()) {
                        let args = tail
                            .join(&format!(" {} ", head));
                        format!("({})", args)
                    } else {
                        format!("{} {}", head, args)
                    }
                },
                _ => String::from("")
            };
            Ok(result)
        },
        ParseNode::Number(node)
        | ParseNode::Symbol(node)
        | ParseNode::String(node) =>
            Ok(if node.value.chars().any(|c| c.is_whitespace()) {
                format!("\"{}\"", node.value)
            } else {
                node.value.to_owned()
            }),
        ParseNode::Attribute(_) => Err(GenerationError::new("CSS-value",
                "Incompatible structure (attribute) found in CSS \
                 property value.",
                &node.site()))
    }
}

/// Function responsible for translating a CSS value (i.e.
/// a value of a CSS property) from some s-expression into
/// a valid CSS value.
pub fn css_value(_property : &str, node : &ParseNode)
-> Result<String, GenerationError> {
    // Naïve way (in future consider the type of property,
    //  and take care of special cases):
    convert_value(node)
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
                                     css_value(&property.keyword, value)?)?;
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

