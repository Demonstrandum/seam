//! Assembles an expanded tree into valid CSS.
use super::{child_whitespace, GenerationError, MarkupFormatter, Formatter};
use crate::parse::{parser::{ParseNode, ParseTree}, tokens::Site};

use std::slice::Iter;

#[derive(Debug, Clone)]
pub struct CSSFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> CSSFormatter<'a> {
    /// Generate a sequence of CSS rules.
    pub fn generate_nodes(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for node in nodes {
            Self::generate_node(f, node, node.leading_whitespace())?;
        }
        Ok(())
    }

    /// Generate the rules within an element (see [`child_whitespace`]).
    pub fn generate_children(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for (index, node) in nodes.iter().enumerate() {
            Self::generate_node(f, node, child_whitespace(index, node))?;
        }
        Ok(())
    }

    fn generate_node(f: Formatter, node: &ParseNode<'a>, leading: &str) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::List { nodes: list, .. } => {
                write!(f, "{leading}")?;
                generate_css_rule(f, list.iter())?;
            },
            ParseNode::Attribute { site, .. }  => {
                return Err(GenerationError::new("CSS",
                    "Attribute not expected here, CSS documents \
                     are supposed to be a series of selectors \
                     and property-value pairs, wrapped in parentheses.",
                     &site.to_owned()));
            },
            // Raw text (e.g. hand-written CSS around literate macro calls) is written as it is.
            ParseNode::Raw(node) => {
                write!(f, "{leading}{}", node.value)?;
            },
            ParseNode::Symbol(node)
            | ParseNode::Number(node)
            | ParseNode::String(node) => {
                let site = node.site;
                return Err(GenerationError::new("CSS",
                    "Symbolic node not expected here, CSS documents \
                     are supposed to be a series of selectors \
                     and property-value pairs, wrapped in parentheses.",
                     &site));
            }
        }
        Ok(())
    }

    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self { tree }
    }
}

pub const DEFAULT: &str = "\n";

/// All CSS functions, I might have missed a few.
const CSS_FUNCTIONS: [&str; 58] = [
    "attr", "blur", "brightness", "calc", "circle", "color", "contrast",
    "counter", "counters", "cubic-bezier", "drop-shadow", "ellipse", "format",
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
const CSS_COMMA_DELIM: [&str; 2] = ["rgba", "hsla"];

/// Intentionally left out "@viewport".  If they decided to make
/// CSS a good and coherent language in the first place, we wouldn't
/// have to deal with ridiculous stuff like this.
const CSS_SPECIAL_SELECTORS: [&str; 12]
    = [ "@charset"   , "@counter-style"       , "@document"
      , "@font-face" , "@font-feature-values" , "@import"
      , "@keyframes" , "@media"               , "@namespace"
      , "@page"      , "@property"            , "@supports"
      ];

/// Special selectors that do not have a body.
const CSS_ONELINE_RULES: [&str; 3]
    = [ CSS_SPECIAL_SELECTORS[0]  //< @charset
      , CSS_SPECIAL_SELECTORS[5]  //< @import
      , CSS_SPECIAL_SELECTORS[8]  //< @namespace
      ];

/// Special selectors that do not have nested selectors as their body.
const CSS_NON_NESTED_SELECTORS: [&str; 3]
    = [ CSS_SPECIAL_SELECTORS[3]  //< @font-face
      , CSS_SPECIAL_SELECTORS[9]  //< @page
      , CSS_SPECIAL_SELECTORS[10] //< @property
      ];

/// The only four math operations supported by CSS calc(...),
/// or at least I think.
const BINARY_OPERATORS: [&str; 4] = ["+", "-", "*", "/"];

fn convert_value<'a>(node: &ParseNode<'a>) -> Result<String, GenerationError<'a>> {
    match node {
        ParseNode::List { nodes: list, .. } => {
            let result = match &**list {
                [head, tail@..] => {
                    let head = convert_value(head)?;

                    let mut tail_tmp = vec![String::new(); tail.len()];
                    for (i, e) in tail.iter().enumerate() {
                        tail_tmp[i] = convert_value(e)?;
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
                        format!("{head}({args})")
                    } else if BINARY_OPERATORS.contains(&head.as_str()) {
                        let args = tail
                            .join(&format!(" {head} "));
                        format!("({args})")
                    } else {
                        format!("{head} {args}")
                    }
                },
                [] => String::new()
            };
            Ok(result)
        },
        ParseNode::Number(node)
        | ParseNode::Symbol(node)
        | ParseNode::String(node) =>
            Ok(if node.value.chars().any(char::is_whitespace) {
                format!("{:?}", node.value)
            } else {
                node.value.to_string()
            }),
        ParseNode::Raw(node) => {
            Ok(node.value.to_string())
        },
        ParseNode::Attribute { .. } => Err(GenerationError::new("CSS-value",
                "Incompatible structure (attribute) found in CSS \
                 property value.",
                node.site()))
    }
}

/// Function responsible for translating a CSS value (i.e.
/// a value of a CSS property) from some s-expression into
/// a valid CSS value.
pub fn css_value<'a>(_property: &str, node: &ParseNode<'a>)
-> Result<String, GenerationError<'a>> {
    // Naïve way (in future consider the type of property,
    //  and take care of special cases):
    convert_value(node)
}

/// # A special-selector / @-rule looks like:
/// S-expr:                          CSS:
/// (@symbol arg)                      -> @symbol arg;
/// (@symbol :attr arg)                -> @symbol (attr: arg); OR @symbol { attr: arg }
/// (@symbol (select :prop val))       -> @symbol { select { prop: val; } }
/// (@sym x :attr arg (sel :prop val)) -> @sym x (attr: arg) { sel { prop: val; } }
fn generate_special_selector<'b, 'a>(f: Formatter,
                                 selector: &str,
                                 mut arguments: Iter<'b, ParseNode<'a>>)
-> Result<(), GenerationError<'a>> {
    let mut parsing_rules: bool = false;
    let unexpected_node = |node: &'b ParseNode<'a>, rules: bool| {
        if rules {
            Err(GenerationError::new("CSS",
                "Expected list (i.e. a CSS rule) here!",
                node.site()))
        } else {
            Ok(())
        }
    };
    // Deal with one-line rules quickly.
    if CSS_ONELINE_RULES.contains(&selector) {
        write!(f, "{selector} ")?;
        arguments.next();  // Skip `@`-selector.
        for arg in arguments {
            match arg {
                ParseNode::Attribute { keyword, node, .. } => {
                    write!(f, "({}: {}) ", keyword, css_value(keyword, node)?)?;
                },
                _ => write!(f, "{} ", css_value(selector, arg)?)?
            }
        }
        writeln!(f, ";")?;
        return Ok(());
    }

    // Handle @-rules with nested elements.
    write!(f, "{selector} ")?;
    arguments.next();  // Skip `@`-selector.

    for arg in arguments {
        match arg {
            ParseNode::Attribute { keyword, node, .. } => {
                unexpected_node(arg, parsing_rules)?;
                write!(f, "({}: {}) ", keyword, css_value(keyword, node)?)?;
            },
            ParseNode::List { nodes: rule, leading_whitespace, .. } => {
                // Now we parse nested rules!
                if !parsing_rules {
                    writeln!(f, "{{")?;
                }
                parsing_rules = true;
                write!(f, "{leading_whitespace}")?;
                generate_css_rule(f, rule.into_iter())?;
            },
            _ => {
                unexpected_node(arg, parsing_rules)?;
                write!(f, "{} ", css_value(selector, arg)?)?;
            }
        }
    }
    write!(f, "}}")?;
    Ok(())
}

/// The argument to a selector function, e.g. `(+ 2n 1)` -> `2n + 1`.
fn selector_argument<'a>(node: &ParseNode<'a>) -> Result<String, GenerationError<'a>> {
    if let ParseNode::List { nodes, .. } = node
    && let [head, tail@..] = &**nodes
    && let Some(op) = head.atomic().filter(|op| BINARY_OPERATORS.contains(&op.value.as_ref())) {
        // Unlike in values, an+b syntax may not be parenthesised.
        let tail = tail.iter().map(convert_value).collect::<Result<Vec<_>, _>>()?;
        return Ok(tail.join(&format!(" {} ", op.value)));
    }
    convert_value(node)
}

fn generate_css_rule<'a>(f: Formatter, iter: Iter<'_, ParseNode<'a>>) -> Result<(), GenerationError<'a>> {
    // Collect the selectors: symbols, along with selector functions written
    // as a list of attributes, e.g. `(ul li(:nth-child (+ 2n 1)))` -> `ul li:nth-child(2n + 1)`.
    let mut nodes = iter.as_slice();
    let mut selector = String::new();
    let mut head = None;
    while let Some((node, rest)) = nodes.split_first() {
        match node {
            ParseNode::List { nodes: functions, leading_whitespace, .. } if head.is_some()
                && !functions.is_empty()
                && functions.iter().all(|function| matches!(function, ParseNode::Attribute { .. })) => {
                // Written apart from the preceding selector, it selects descendants.
                if !leading_whitespace.is_empty() {
                    selector.push(' ');
                }
                for function in functions {
                    let ParseNode::Attribute { keyword, node, .. } = function else { unreachable!() };
                    selector += ":";
                    selector += keyword;
                    selector += "(";
                    selector += &selector_argument(node)?;
                    selector += ")";
                }
            },
            _ => {
                let Some(atom) = node.atomic() else { break };
                if head.is_some() {
                    selector.push(' ');
                }
                head.get_or_insert(atom);
                selector += &atom.value;
            },
        }
        nodes = rest;
    }

    // Check we were actually provided with
    // some selectors.
    let Some(head) = head else {
        // Point at the rule's first (non-selector) node, if there is one.
        let site = iter.clone().next().map_or_else(Site::unknown, ParseNode::owned_site);
        return Err(GenerationError::new("CSS",
            "CSS selector(s) missing. \
             Expected a symbol/identifier node, none was found!",
             &site));
    };

    // Handle special @-rule selectors.
    if CSS_SPECIAL_SELECTORS.contains(&head.value.as_ref())
    && !CSS_NON_NESTED_SELECTORS.contains(&head.value.as_ref()) {
        // Don't do anything special for non-nested selectors.
        return generate_special_selector(f, &head.value, iter);
    }

    writeln!(f, "{selector} {{")?;

    for property in nodes {
        let ParseNode::Attribute { node, keyword, .. } = property else {
            return Err(GenerationError::new("CSS",
                "CSS property-value pairs must be in the \
                 form of attributes, i.e. `:property value`.",
                 property.site()));
        };
        writeln!(f, "  {}: {};", keyword, css_value(keyword, node)?)?;
    }
    write!(f, "}}")?;
    Ok(())
}

impl<'a> MarkupFormatter<'a> for CSSFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError<'a>> {
        let mut doc = String::new();
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }
        doc += &self.display()?;
        Ok(doc)
    }

    fn generate(&self, f: Formatter)
    -> Result<(), GenerationError<'a>> {
        Self::generate_nodes(f, &self.tree)
    }
}
