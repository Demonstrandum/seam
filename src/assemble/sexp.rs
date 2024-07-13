//! Output expanded source-code as identical looking to the original
//! hand-written code as possible.
use std::cell::RefCell;

use super::{MarkupFormatter, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct SExpFormatter<'a> {
    pub tree: ParseTree<'a>,
    formatters: RefCell<Vec<Box<dyn MarkupFormatter + 'a>>>,
}

impl<'a> SExpFormatter<'a> {
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree,
            formatters: Default::default()
        }
    }

    fn register_formatter<Fmt: MarkupFormatter + 'a>(&self, formatter: Fmt) -> &'a Box<dyn MarkupFormatter + 'a> {
        let fmts = self.formatters.as_ptr();
        unsafe {
            (*fmts).push(Box::new(formatter));
            (*fmts).last().unwrap()
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
            ParseNode::List { nodes, leading_whitespace, end_token, .. } => {
                write!(f, "{}", leading_whitespace)?;
                write!(f, "(")?;
                let tree = nodes.to_vec();
                let sexp_fmt = SExpFormatter::new(tree.into_boxed_slice());
                let sexp_fmt = self.register_formatter(sexp_fmt);
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

impl<'a> MarkupFormatter for SExpFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError> {
        self.display()
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError> {
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            self.generate_node(f, node)?;
        }
        Ok(())
    }
}
