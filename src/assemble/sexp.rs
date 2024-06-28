//! Output expanded source-code as identical looking to the original
//! hand-written code as possible.

use super::{MarkupDisplay, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct SExpFormatter<'a> {
    pub tree : ParseTree<'a>,
}

impl<'a> SExpFormatter<'a> {
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self { tree }
    }
}

impl<'a> MarkupDisplay for SExpFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError> {
        self.display()
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError> {
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            generate_node(f, node)?;
        }
        Ok(())
    }
}

// TODO: Make this into a trait on `ParseNode`?
/// Write S-expression string for a single parse node into formatter.
fn generate_node<'a>(f: Formatter, node: &ParseNode<'a>) -> Result<(), GenerationError<'a>> {
    match node {
        ParseNode::Symbol(node)
      | ParseNode::Number(node) => {
            write!(f, "{}", node.leading_whitespace)?;
            write!(f, "{}", node.value)?;
        },
        ParseNode::String(node) => {
            // We actually don't want the rendered string,
            // we want the escaped string, so we retrieve
            // it from source.
            write!(f, "{}", node.leading_whitespace)?;
            write!(f, "{}", node.site.view())?;
        },
        ParseNode::List { nodes, leading_whitespace, end_token, .. } => {
            write!(f, "{}", leading_whitespace)?;
            write!(f, "(")?;
            let tree = nodes.to_vec();
            let sexp_fmt = SExpFormatter::new(tree.into_boxed_slice());
            let sexp_fmt = Box::leak(Box::new(sexp_fmt)); // FIXME: Store.
            sexp_fmt.generate(f)?;
            write!(f, "{}", end_token.leading_whitespace)?;
            write!(f, ")")?;

        },
        ParseNode::Attribute { keyword, node, leading_whitespace, .. } => {
            write!(f, "{}", leading_whitespace)?;
            write!(f, ":{}", keyword)?;
            generate_node(f, node)?;
        },
    }
    Ok(())
}
