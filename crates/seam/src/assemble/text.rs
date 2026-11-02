//! Output expanded plain-text.
//! Very similar to the source-code expanding SExp generator,
//! but this also converts strings and other constructs
//! into unescaped plain text as well.

use super::{child_whitespace, MarkupFormatter, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct PlainTextFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> PlainTextFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    /// Generate a sequence of nodes.
    pub fn generate_nodes(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for node in nodes {
            Self::generate_node(f, node, node.leading_whitespace())?;
        }
        Ok(())
    }

    /// Generate the children of an element (see [`child_whitespace`]).
    pub fn generate_children(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for (index, node) in nodes.iter().enumerate() {
            Self::generate_node(f, node, child_whitespace(index, node))?;
        }
        Ok(())
    }

    fn generate_node(f: Formatter, node: &ParseNode<'a>, leading: &str) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
          | ParseNode::Number(node)
          | ParseNode::String(node)
          | ParseNode::Raw(node) => {
                write!(f, "{leading}")?;
                write!(f, "{}", node.value)?;
            },
            ParseNode::List { nodes, end_token, .. } => {
                write!(f, "{leading}")?;
                write!(f, "(")?;
                Self::generate_nodes(f, nodes)?;
                write!(f, "{}", end_token.leading_whitespace)?;
                write!(f, ")")?;

            },
            ParseNode::Attribute { keyword, node, .. } => {
                write!(f, "{leading}")?;
                write!(f, ":{keyword}")?;
                Self::generate_node(f, node, node.leading_whitespace())?;
            },
        }
        Ok(())
    }
}

impl<'a> MarkupFormatter<'a> for PlainTextFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError<'a>> {
        self.display()
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError<'a>> {
        Self::generate_nodes(f, &self.tree)
    }
}
