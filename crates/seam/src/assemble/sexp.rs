//! Output expanded source-code as identical looking to the original
//! hand-written code as possible.

use super::{child_whitespace, MarkupFormatter, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct SExpFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> SExpFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    /// Generate a sequence of nodes.
    pub fn generate_nodes(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for (index, node) in nodes.iter().enumerate() {
            let leading = node.leading_whitespace();
            // Expanded nodes may lack whitespace, which would join adjacent items.
            let separate = leading.is_empty() && index > 0;
            Self::generate_node(f, node, if separate { " " } else { leading })?;
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
          | ParseNode::Number(node) => {
                write!(f, "{leading}")?;
                write!(f, "{}", node.value)?;
            },
            ParseNode::String(node) => {
                // We actually don't want the rendered string with the escpaes
                // that we parsed, so we send it to the debug view to get a string
                // with quotes and escaped special characters.
                write!(f, "{leading}")?;
                write!(f, "{:?}", node.value)?;
            },
            ParseNode::Raw(node) => {
                // This is the only place we can't really expand
                // the `(%raw ...)` macro. It is meaningful.
                write!(f, "{leading}")?;
                write!(f, "(%raw {:?})", node.value)?;
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
                let leading = node.leading_whitespace();
                Self::generate_node(f, node, if leading.is_empty() { " " } else { leading })?;
            },
        }
        Ok(())
    }

}

impl<'a> MarkupFormatter<'a> for SExpFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError<'a>> {
        self.display()
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError<'a>> {
        Self::generate_nodes(f, &self.tree)
    }
}
