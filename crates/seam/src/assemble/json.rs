//! Output JSON, the reverse of reading JSON with `%json`.
//! A list of `:key value` attributes is an object, any other list is an
//! array; strings stay strings, numbers stay numbers, and the symbols
//! `true`, `false` and `null` are themselves.  Other symbols are strings.

use super::{MarkupFormatter, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};
use crate::parse::expander::Number;

#[derive(Debug, Clone)]
pub struct JSONFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> JSONFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    /// Generate the tree as one value: a single value as itself,
    /// otherwise as the items of a list.
    fn generate_tree(&self, f: Formatter, indent: Option<usize>) -> Result<(), GenerationError<'a>> {
        match &*self.tree {
            [node] if !node.is_attribute() => Self::generate_value(f, node, indent),
            nodes => Self::generate_items(f, nodes, indent),
        }
    }

    /// Generate a value, indenting nested lines by `indent` levels when pretty.
    pub fn generate_value(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::String(node) => write_string(f, &node.value)?,
            ParseNode::Raw(node) => write!(f, "{}", node.value)?,
            ParseNode::Symbol(node) => match node.value.as_ref() {
                "true" | "false" | "null" => write!(f, "{}", node.value)?,
                _ => write_string(f, &node.value)?,
            },
            ParseNode::Number(atom) => match Number::of(node) {
                Some(Number::Int(int)) => write!(f, "{int}")?,
                Some(Number::Float(float)) if float.is_finite() => write!(f, "{float}")?,
                _ => return Err(GenerationError::new("JSON",
                    &format!("`{}' is not a number JSON can represent.", atom.value), &atom.site)),
            },
            ParseNode::List { nodes, .. } => Self::generate_items(f, nodes, indent)?,
            ParseNode::Attribute { site, .. } => return Err(GenerationError::new("JSON",
                "A keyword attribute can only be part of an object (a list of attributes).", site)),
        }
        Ok(())
    }

    /// Generate the items of a list, as an object if they are all
    /// attributes, or as an array if none are.
    fn generate_items(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<(), GenerationError<'a>> {
        let object = nodes.first().is_some_and(ParseNode::is_attribute);
        if let Some(odd) = nodes.iter().find(|node| node.is_attribute() != object) {
            return Err(GenerationError::new("JSON", if object {
                "An object (a list of attributes) cannot also have plain items."
            } else {
                "An array (a list of plain items) cannot also have keyword attributes."
            }, odd.site()));
        }
        let (open, close) = if object { ("{", "}") } else { ("[", "]") };
        write!(f, "{open}")?;
        let inner = indent.map(|indent| indent + 1);
        for (index, node) in nodes.iter().enumerate() {
            if index > 0 {
                write!(f, ",")?;
            }
            newline(f, inner)?;
            if let ParseNode::Attribute { keyword, node, .. } = node {
                write_string(f, keyword)?;
                write!(f, "{}", if indent.is_some() { ": " } else { ":" })?;
                Self::generate_value(f, node, inner)?;
            } else {
                Self::generate_value(f, node, inner)?;
            }
        }
        if !nodes.is_empty() {
            newline(f, indent)?;
        }
        write!(f, "{close}")?;
        Ok(())
    }
}

/// Start a new line at an indentation level, when pretty-printing.
fn newline(f: Formatter, indent: Option<usize>) -> std::fmt::Result {
    match indent {
        Some(indent) => write!(f, "\n{:width$}", "", width = 2 * indent),
        None => Ok(()),
    }
}

/// Write a JSON string literal.
fn write_string(f: Formatter, text: &str) -> std::fmt::Result {
    write!(f, "\"")?;
    let mut previous = '\0';
    for c in text.chars() {
        match c {
            '"' => write!(f, "\\\"")?,
            '\\' => write!(f, "\\\\")?,
            // So `</script>` in a string cannot end a script it is embedded in.
            '/' if previous == '<' => write!(f, "\\/")?,
            '\n' => write!(f, "\\n")?,
            '\r' => write!(f, "\\r")?,
            '\t' => write!(f, "\\t")?,
            '\u{08}' => write!(f, "\\b")?,
            '\u{0C}' => write!(f, "\\f")?,
            c if c < ' ' => write!(f, "\\u{:04x}", c as u32)?,
            c => write!(f, "{c}")?,
        }
        previous = c;
    }
    write!(f, "\"")
}

impl<'a> MarkupFormatter<'a> for JSONFormatter<'a> {
    /// A document is indented, one item per line.
    fn document(&self) -> Result<String, GenerationError<'a>> {
        let mut buf = String::new();
        self.generate_tree(&mut buf, Some(0))?;
        Ok(buf)
    }

    /// Otherwise, it is compact, on one line.
    fn generate(&self, f: Formatter) -> Result<(), GenerationError<'a>> {
        self.generate_tree(f, None)
    }
}
