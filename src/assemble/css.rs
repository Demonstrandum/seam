//! Assembles an expanded tree into valid CSS.
use super::{GenerationError, MarkupDisplay, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

use std::slice::Iter;

#[derive(Debug, Clone)]
pub struct CSSFormatter<'a> {
    pub tree : ParseTree<'a>,
}

impl<'a> CSSFormatter<'a> {
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self { tree }
    }
}

pub const DEFAULT : &str = "\n";

/// All CSS functions, I might have missed a few.
const CSS_FUNCTIONS : [&str; 57] = [
    "attr", "blur", "brightness", "calc", "circle", "color", "contrast",
    "counter", "counters", "cubic-bezier", "drop-shadow", "ellipse",
    "grayscale", "hsl", "hsla", "hue-rotate", "hwb", "image", "inset",
    "invert", "lab", "lch", "linear-gradient", "matrix", "matrix3d",
    "opacity", "perspective", "polygon", "radial-gradient",
    "repeating-linear-gradient", "repeating-radial-gradient",
    "rgb", "rgba", "rotate", "rotate3d", "rotateX",
    "rotateY", "rotateZ", "saturate", "sepia", "scale", "scale3d",
    "scaleX", "scaleY", "scaleZ", "skew", "skewX", "skewY", "symbols",
    "translate", "translate3d", "translateX", "translateY", "translateZ",
    "url", "var", "supports"
];

/// Some CSS functions use commas as an argument delimiter,
/// some use spaces!  Why not!
const CSS_COMMA_DELIM : [&str; 2] = ["rgba", "hsla"];

/// Intentionally left out "@viewport".  If they decided to make
/// CSS a good and coherent language in the first place, we wouldn't
/// have to deal with ridiculous stuff like this.
const CSS_SPECIAL_SELECTORS : [&str; 12]
    = [ "@charset"   , "@counter-style"       , "@document"
      , "@font-face" , "@font-feature-values" , "@import"
      , "@keyframes" , "@media"               , "@namespace"
      , "@page"      , "@property"            , "@supports"
      ];

/// Special selectors that do not have a body.
const CSS_ONELINE_RULES : [&str; 3]
    = [ CSS_SPECIAL_SELECTORS[0]  //< @charset
      , CSS_SPECIAL_SELECTORS[5]  //< @import
      , CSS_SPECIAL_SELECTORS[8]  //< @namespace
      ];

/// The only four math operations supported by CSS calc(...),
/// or at least I think.
const BINARY_OPERATORS : [&str; 4] = ["+", "-", "*", "/"];

fn convert_value<'a>(node: &'a ParseNode<'a>) -> Result<String, GenerationError<'a>> {
    match node {
        ParseNode::List { nodes: list, .. } => {
            let result = match &**list {
                [head, tail@..] => {
                    let head = convert_value(head)?;

                    let mut tail_tmp = vec![String::new(); tail.len()];
                    for (i, e) in tail.iter().enumerate() {
                        tail_tmp[i] = convert_value(e)?
                    }
                    let tail = tail_tmp.as_slice();

                    let delim = if CSS_COMMA_DELIM.contains(&head.as_str()) {
                        ", "
                    } else {
                        " "
                    };
                    let args = tail.join(delim);
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
                [] => String::from("")
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
        ParseNode::Attribute { .. } => Err(GenerationError::new("CSS-value",
                "Incompatible structure (attribute) found in CSS \
                 property value.",
                &node.site()))
    }
}

/// Function responsible for translating a CSS value (i.e.
/// a value of a CSS property) from some s-expression into
/// a valid CSS value.
pub fn css_value<'a>(_property : &str, node: &'a ParseNode<'a>)
-> Result<String, GenerationError<'a>> {
    // Naïve way (in future consider the type of property,
    //  and take care of special cases):
    convert_value(node)
}

/// # A special-selector / @-rule looks like:
/// S-expr:                          CSS:
/// (@symbol arg)                      -> @symbol arg;
/// (@symbol :attr arg)                -> @symbol (attr: arg);
/// (@symbol (select :prop val))       -> @symbol { select { prop: val; } }
/// (@sym x :attr arg (sel :prop val)) -> @sym x (attr: arg) { sel { prop: val; } }
fn generate_special_selector<'a>(f: Formatter,
    selector: &str,
    arguments: Iter<'a, ParseNode<'a>>)
    -> Result<(), GenerationError<'a>> {
    // Deal with oneline rules quickly.
    if CSS_ONELINE_RULES.contains(&selector) {
        write!(f, "{} ", selector)?;
        for arg in arguments {
            match arg {
                ParseNode::Attribute { ref keyword, node, .. } => {
                    write!(f, "({}: {}) ", keyword, css_value(keyword, &*node)?)?;
                },
                _ => write!(f, "{} ", css_value(selector, arg)?)?
            }
        }
        writeln!(f, ";")?;
        return Ok(());
    }
    // @-rules with nested elements!
    write!(f, "{} ", selector)?;

    let mut parsing_rules = false;
    let unexpected_node = |node: &'a ParseNode<'a>, rules: bool| {
        if rules {
            Err(GenerationError::new("CSS",
                "Expected list (i.e. a CSS rule) here!",
                &node.site()))
        } else {
            Ok(())
        }
    };

    for arg in arguments {
        match arg {
            ParseNode::Attribute { ref keyword, node, .. } => {
                unexpected_node(&arg, parsing_rules)?;
                write!(f, "({}: {}) ", keyword, css_value(keyword, &*node)?)?;
            },
            ParseNode::List { nodes: ref rule, leading_whitespace, .. } => {
                // Now we parse nested rules!
                if !parsing_rules {
                    writeln!(f, "{{")?;
                }
                parsing_rules = true;
                write!(f, "{}", leading_whitespace)?;
                generate_css_rule(f, rule)?;
            },
            _ => {
                unexpected_node(&arg, parsing_rules)?;
                write!(f, "{} ", css_value(selector, arg)?)?;
            }
        }
    }
    write!(f, "}}")?;
    Ok(())
}

fn generate_css_rule<'a>(f: Formatter, list: &'a [ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
    let mut iter = list.iter();
    let mut prop_i = 0; // Index of first property.
    // TODO: Selector functions such as nth-child(...), etc.
    // e.g. (ul li(:nth-child (+ 2n 1))) -> ul li:nth-child(2n + 1).
    let mut selectors = iter.clone()
        .take_while(|n| { prop_i += 1; n.atomic().is_some() })
        .map(|n| n.atomic().unwrap()) // We've checked.
        .peekable();

    // Check we were actually provided with
    // some selectors.
    let head = if let Some(head) = selectors.next() {
        head
    } else {
        return Err(GenerationError::new("CSS",
            "CSS selector(s) missing. \
             Expected a symbol/identifier node, none was found!",
             &list[0].site()));
    };

    // Handle special @-rule selectors.
    if CSS_SPECIAL_SELECTORS.contains(&head.value.as_ref()) {
        iter.next();  //< Throw away the head.
        return generate_special_selector(f, &head.value, iter);
    }

    // Join the selectors togeher.
    write!(f, "{} ", head.value)?;
    for selector in selectors {
        write!(f, "{} ", selector.value)?;
    }
    writeln!(f, "{{")?;

    let properties = iter.skip(prop_i - 1);

    for property in properties {
        let ParseNode::Attribute { ref node, ref keyword, .. } = property else {
            return Err(GenerationError::new("CSS",
                "CSS property-value pairs must be in the \
                 form of attributes, i.e. `:property value`.",
                 &property.site()));
        };
        writeln!(f, "  {}: {};", keyword, css_value(keyword, node)?)?;
    }
    write!(f, "}}")?;
    Ok(())
}

impl<'a> MarkupDisplay for CSSFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError> {
        let mut doc = String::new();
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }
        doc += &self.display()?;
        Ok(doc)
    }

    fn generate(&self, f: Formatter)
    -> Result<(), GenerationError> {
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            match node {
                ParseNode::List { nodes: list, leading_whitespace, .. } => {
                    write!(f, "{}", leading_whitespace)?;
                    generate_css_rule(f, &*list)?;
                },
                ParseNode::Attribute { site, .. }  => {
                    return Err(GenerationError::new("CSS",
                        "Attribute not expected here, CSS documents \
                         are supposed to be a series of selectors \
                         and property-value pairs, wrapped in parentheses.",
                         &site.to_owned()));
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
