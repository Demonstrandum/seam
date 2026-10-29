//! Output expanded plain-text.
//! Very similar to the source-code expanding SExp generator,
//! but this also converts strings and other constructs
//! into unescaped plain text as well.

use super::{MarkupFormatter, GenerationError, Formatter};
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

    fn generate_node(f: Formatter, node: &ParseNode<'a>) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
          | ParseNode::Number(node)
          | ParseNode::String(node)
          | ParseNode::Raw(node) => {
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", node.value)?;
            },
            ParseNode::List { nodes, leading_whitespace, end_token, .. } => {
                write!(f, "{leading_whitespace}")?;
                write!(f, "(")?;
                let tree = nodes.to_vec();
                let text_fmt = PlainTextFormatter::new(tree.into_boxed_slice());
                text_fmt.generate(f)?;
                write!(f, "{}", end_token.leading_whitespace)?;
                write!(f, ")")?;

            },
            ParseNode::Attribute { keyword, node, leading_whitespace, .. } => {
                write!(f, "{leading_whitespace}")?;
                write!(f, ":{keyword}")?;
                Self::generate_node(f, node)?;
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
        let tree_iter = self.tree.iter().peekable();
        for node in tree_iter {
            Self::generate_node(f, node)?;
        }
        Ok(())
    }
}
