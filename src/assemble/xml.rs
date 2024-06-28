//! Assembles an expanded tree into valid XML.
use super::{escape_xml, MarkupDisplay, GenerationError, Formatter};
use crate::parse::parser::{self, ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct XMLFormatter<'a> {
    pub tree : ParseTree<'a>,
}

impl<'a> XMLFormatter<'a> {
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self { tree }
    }
}

pub const DEFAULT : &str =
    "<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n";

impl<'a> MarkupDisplay for XMLFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError> {
        let mut doc = String::new();
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }
        let current_node = self.tree.get(0);

        // Check if declaration exists.
        let mut has_declaration = false;
        if let Some(ParseNode::List { nodes: list, .. }) = current_node.as_ref() {
            if let Some(ParseNode::Symbol(declaration)) = list.get(0) {
                if declaration.value.to_lowercase() == "?xml" {
                    has_declaration = true;
                }
            }
        }

        if !has_declaration {
            doc += DEFAULT;
        }

        // Populate.
        doc += &self.display()?;
        Ok(doc)
    }

    fn generate(&self, f : Formatter) -> Result<(), GenerationError> {
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            generate_xml_node(f, node)?;
        }
        Ok(())
    }
}

fn generate_xml_node<'a>(f: Formatter, node: &'a ParseNode<'a>) -> Result<(), GenerationError<'a>> {
    match node {
        ParseNode::Symbol(node)
        | ParseNode::Number(node) => {
            write!(f, "{}", node.leading_whitespace)?;
            write!(f, "{}", escape_xml(&node.value))?;
        },
        ParseNode::String(node) => {
            write!(f, "{}", node.leading_whitespace)?;
            write!(f, "{}", escape_xml(&node.value))?
        },
        ParseNode::List { nodes: list, leading_whitespace, end_token, .. } => {
            write!(f, "{}", leading_whitespace)?;
            let head = list.first();
            let tag: &str;  // xml <tag> name.
            if let Some(head_node) = head {
                if let ParseNode::Symbol(head_symbol) = head_node {
                    tag = &head_symbol.value;
                    write!(f, "<{}", tag)?;
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
                    } else if let attr@ParseNode::Attribute { .. } = &rest[0] {
                        write!(f, " {}", display_attribute(attr)?)?;
                    } else {
                        return Err(GenerationError::new("XML",
                            "Only identifiers and attributes are allowed in declarations.",
                            &rest[0].site()));
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

            while let Some(attr@ParseNode::Attribute { .. }) = rest.first() {
                write!(f, " {}", display_attribute(&attr)?)?;
                rest = &rest[1..];
            }
            write!(f, ">")?;

            // See similar comment for HTML generation:
            // We strip leading whitespace from the first child element in a tag.
            // This is more natural w.r.t. the S-exp syntax.
            let mut rest = rest.to_vec();
            let mut is_first_node_on_next_line = false;
            if let Some(first_node) = rest.get_mut(0) {
                is_first_node_on_next_line = first_node.leading_whitespace().contains('\n');
                if !is_first_node_on_next_line {
                    first_node.set_leading_whitespace("".to_owned());
                }
            }

            let xml_fmt = XMLFormatter::new(rest.to_owned().into_boxed_slice());
            let xml_fmt = Box::leak(Box::new(xml_fmt)); // FIXME: store formatter.
            xml_fmt.generate(f)?;

            // Closing tag should be equally as spaced as opening tag (?)
            if end_token.leading_whitespace.is_empty() {
                if is_first_node_on_next_line || tag == "style" {
                    write!(f, "{}", leading_whitespace)?;
                }
            } else {
                write!(f, "{}", end_token.leading_whitespace)?;
            }

            write!(f, "</{}>", tag)?;
        },
        _ => return Err(GenerationError::new("XML",
                &format!("Unexpected {} node when generating.", node.node_type()),
                &node.site()))
    }
    Ok(())
}

fn display_attribute<'a>(attr: &'a parser::ParseNode<'a>) -> Result<String, GenerationError> {
    let parser::ParseNode::Attribute { keyword, node, .. } = attr else {
        panic!("Passed non-attribute to display_attribute.")
    };
    if let Some(symbol) = (*node).atomic() {
        Ok(format!("{}=\"{}\"", keyword, symbol.value))
    } else {
        Err(GenerationError::new("XML",
            "Attribute can only contain symbols, numbers or strings",
            &(*node).site()))
    }
}
