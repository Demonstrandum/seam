use super::parser::{ParseNode, ParseTree, Node};
use super::tokens::Site;

use std::{fmt, path::Path, error::Error};

use colored::*;

/// Error type for errors while expanding macros.
#[derive(Debug, Clone)]
pub struct ExpansionError(pub String, pub Site);

impl ExpansionError {
    /// Create a new error given the ML, the message, and the site.
    pub fn new(msg : &str, site : &Site) -> Self {
        Self(msg.to_owned(), site.to_owned())
    }
}

/// Implement fmt::Display for user-facing error output.
impl fmt::Display for ExpansionError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] Error Expanding Macro {}: {}",
            "**".red().bold(), self.1, self.0)
    }
}

/// Implements std::error::Error.
impl Error for ExpansionError { }

use std::collections::HashMap;

#[allow(dead_code)]
struct Macro {
    name : String,
    params : Vec<String>,
    body : ParseNode
}

struct ExpansionContext {
    #[allow(dead_code)] // TODO: User macros!
    definitions : HashMap<String, Macro>
}

impl ExpansionContext {
    pub fn new() -> Self { Self { definitions: HashMap::new() } }

    fn expand_invocation(&mut self, name : &str,
                         site : &Site,
                         params : Vec<ParseNode>)
    -> Result<ParseTree, ExpansionError> {
        match name {
            "include" => {
                let path_node = if let [ p ] = params.as_slice() {
                    p
                } else {
                    return Err(ExpansionError::new(
                        &format!("Incorrect number of arguments \
                            to `{}' macro. Got {}, expected {}.",
                            name, params.len(), 1),
                        site));
                };

                let path = if let Some(node) = path_node.atomic() {
                    node.value
                } else {
                    return Err(ExpansionError::new(
                        &format!("Bad argument to `{}' macro.\n\
                            Expected a path, but did not get any value
                            that could be interpreted as a path.", name),
                        site))
                };

                // Open file, and parse contents!
                let tree = match super::parse_file(&Path::new(&path)) {
                    Ok(tree) => tree,
                    Err(error) => {
                        eprintln!("{}", error);
                        return Err(ExpansionError::new(
                            &format!("Error parsing file `{}' from \
                            `include' macro invocation.", path),
                        site))
                    }
                };

                let mut expanded_tree = Vec::with_capacity(tree.len());
                for branch in tree {
                    expanded_tree.extend(self.expand_node(branch)?);
                }
                Ok(expanded_tree)
            },
            _ => Err(ExpansionError::new(
                    &format!("Macro not found (`{}').", name),
                    site))

        }
    }

    pub fn expand_node(&mut self, node : ParseNode)
    -> Result<ParseTree, ExpansionError> {
        match node {
            ParseNode::Symbol(ref _sym) => {
                // Check if symbol starts with %... and replace it
                // with it's defined value.
                Ok(vec![node])
            },
            ParseNode::List(list) => {
                // Check for macro invocation (%... _ _ _).
                // Recurse over every element.
                let len = list.len();
                let mut call = list.into_iter();
                let head = call.next();

                if let Some(ParseNode::Symbol(ref sym)) = head {
                    if sym.value.starts_with("%") {
                        // Rebuild node...
                        let name = &sym.value[1..];
                        let Node { site, .. } = sym;
                        let params = call.collect();
                        return self.expand_invocation(name, site, params);
                    }
                }

                // Rebuild node...
                let mut expanded_list = Vec::with_capacity(len);
                expanded_list.extend(self.expand_node(head.unwrap())?);
                for elem in call {
                    expanded_list.extend(self.expand_node(elem)?);
                }

                Ok(vec![ParseNode::List(expanded_list)])
            },
            ParseNode::Attribute(mut attr) => {
                let mut expanded_nodes = self.expand_node(*attr.node)?;
                attr.node = Box::new(expanded_nodes[0].clone());
                expanded_nodes[0] = ParseNode::Attribute(attr);
                Ok(expanded_nodes)
            },
            _ => Ok(vec![node])
        }
    }
}

/// Macro-expansion phase.
/// Macros start with `%...'.
pub fn expand(tree : ParseTree) -> Result<ParseTree, ExpansionError> {
    let mut context = ExpansionContext::new();

    let mut expanded = Vec::with_capacity(tree.len());
    for branch in tree {
        expanded.extend(context.expand_node(branch)?);
    }
    Ok(expanded)
}
