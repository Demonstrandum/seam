//! Output expanded source-code as identical looking to the original
//! hand-written code as possible.

use super::{MarkupFormatter, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct SExpFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> SExpFormatter<'a> {
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    fn generate_node(&self, f: Formatter, node: &ParseNode<'a>) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
          | ParseNode::Number(node) => {
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", node.value)?;
            },
            ParseNode::String(node) => {
                // We actually don't want the rendered string with the escpaes
                // that we parsed, so we send it to the debug view to get a string
                // with quotes and escaped special characters.
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{:?}", node.value)?;
            },
            ParseNode::Raw(node) => {
                // This is the only place we can't really expand
                // the `(%raw ...)` macro. It is meaningful.
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "(%raw {:?})", node.value)?;
            },
            ParseNode::List { nodes, leading_whitespace, end_token, .. } => {
                write!(f, "{}", leading_whitespace)?;
                write!(f, "(")?;
                let tree = nodes.to_vec();
                let sexp_fmt = SExpFormatter::new(tree.into_boxed_slice());
                sexp_fmt.generate(f)?;
                write!(f, "{}", end_token.leading_whitespace)?;
                write!(f, ")")?;

            },
            ParseNode::Attribute { keyword, node, leading_whitespace, .. } => {
                write!(f, "{}", leading_whitespace)?;
                write!(f, ":{}", keyword)?;
                self.generate_node(f, node)?;
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
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            self.generate_node(f, node)?;
        }
        Ok(())
    }
}
