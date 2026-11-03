//! Assembles an expanded tree into valid XML.

use super::{child_whitespace, write_escaped, MarkupFormatter, GenerationError, Formatter};
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct XMLFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> XMLFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    /// Generate a sequence of nodes.
    pub fn generate_nodes(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for node in nodes {
            Self::generate_xml_node(f, node, node.leading_whitespace())?;
        }
        Ok(())
    }

    /// Generate the children of an element (see [`child_whitespace`]).
    pub fn generate_children(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for (index, node) in nodes.iter().enumerate() {
            Self::generate_xml_node(f, node, child_whitespace(index, node))?;
        }
        Ok(())
    }

    fn generate_xml_node(f: Formatter, node: &ParseNode<'a>, leading: &str) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
            | ParseNode::Number(node)
            | ParseNode::String(node) => {
                write!(f, "{leading}")?;
                write_escaped(f, &node.value)?;
            },
            ParseNode::List { nodes: list, end_token, .. } => {
                write!(f, "{leading}")?;
                let head = list.first();
                let tag: &str;  // xml <tag> name.
                if let Some(head_node) = head {
                    if let ParseNode::Symbol(head_symbol) = head_node {
                        tag = &head_symbol.value;
                        write!(f, "<{tag}")?;
                    } else {
                        // Error, tags can only have symbol values.
                        return Err(GenerationError::new("XML",
                            "XML tags can only be given as symbols.",
                            head_node.site()));
                    }
                } else {
                    // Error, empty tags not supported.
                    return Err(GenerationError::new("XML",
                        "Empty lists cannot be converted into a valid XML tag.",
                        node.site()));
                }

                let mut rest = &list[1..];

                // Declarations behave differently.
                let front = tag.as_bytes()[0] as char;
                if front == '!' || front == '?' {
                    while !rest.is_empty() {
                        if let Some(node) = rest[0].symbolic() {
                            write!(f, "{}", node.value)?;
                        } else if let ParseNode::Attribute { keyword, node, .. } = &rest[0] {
                            generate_attribute(f, keyword, node)?;
                        } else {
                            return Err(GenerationError::new("XML",
                                "Only identifiers and attributes are allowed in declarations.",
                                rest[0].site()));
                        }
                        rest = &rest[1..];
                    }
                    if front == '?' {
                        write!(f, " ?>")?;
                    } else {
                        write!(f, ">")?;
                    }
                    return Ok(());
                }

                while let Some(ParseNode::Attribute { keyword, node, .. }) = rest.first() {
                    generate_attribute(f, keyword, node)?;
                    rest = &rest[1..];
                }
                write!(f, ">")?;

                // See similar comment for HTML generation:
                // We strip leading whitespace from the first child element in a tag.
                // This is more natural w.r.t. the S-exp syntax.
                let is_first_node_on_next_line = rest.first()
                    .is_some_and(|first| first.leading_whitespace().contains('\n'));
                Self::generate_children(f, rest)?;

                // Closing tag should be equally as spaced as opening tag (?)
                if end_token.leading_whitespace.is_empty() {
                    if is_first_node_on_next_line || tag == "style" {
                        write!(f, "{leading}")?;
                    }
                } else {
                    write!(f, "{}", end_token.leading_whitespace)?;
                }

                write!(f, "</{tag}>")?;
            },
            _ => return Err(GenerationError::new("XML",
                    &format!("Unexpected {} node when generating.", node.node_type()),
                    node.site()))
        }
        Ok(())
    }
}

pub const DEFAULT: &str =
    "<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n";

impl<'a> MarkupFormatter<'a> for XMLFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError<'a>> {
        let mut doc = String::new();
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }
        let current_node = self.tree.first();

        // Check if declaration exists.
        let mut has_declaration = false;
        if let Some(ParseNode::List { nodes: list, .. }) = current_node.as_ref()
            && let Some(ParseNode::Symbol(declaration)) = list.first()
                && declaration.value.to_lowercase() == "?xml" {
                    has_declaration = true;
                }

        if !has_declaration {
            doc += DEFAULT;
        }

        // Populate.
        doc += &self.display()?;
        Ok(doc)
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError<'a>> {
        Self::generate_nodes(f, &self.tree)
    }
}

/// Write an attribute, ` keyword="value"`, with its value escaped.
fn generate_attribute<'a>(f: Formatter, keyword: &str, node: &ParseNode<'a>) -> Result<(), GenerationError<'a>> {
    let Some(atom) = node.atomic() else {
        return Err(GenerationError::new("XML",
            "Attribute can only contain symbols, numbers or strings",
            node.site()));
    };
    write!(f, " {keyword}=\"")?;
    write_escaped(f, &atom.value)?;
    write!(f, "\"")?;
    Ok(())
}
