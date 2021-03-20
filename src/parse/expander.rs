use super::parser::{self, ParseNode, ParseTree, Node};
use super::tokens::Site;

use std::{fmt, path::{Path, PathBuf}, ffi::OsString, error::Error};

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

#[derive(Clone)]
struct Macro {
    name : String,
    params : Vec<String>,
    body : Vec<ParseNode>
}

impl Macro {
    fn new(name : &str) -> Macro {
        Macro {
            name: name.to_string(),
            params: Vec::new(),
            body:   Vec::new()
        }
    }
}

#[derive(Clone)]
struct ExpansionContext {
    definitions : HashMap<String, Macro>
}

impl ExpansionContext {
    pub fn new() -> Self { Self { definitions: HashMap::new() } }

    fn expand_invocation(&mut self, name : &str,
                         site : &Site,
                         params : Vec<ParseNode>)
    -> Result<ParseTree, ExpansionError> { match name {
        // Some macros are lazy (e.g. `ifdef`), so each macro has to
        //   expand the macros in its arguments individually.
        "define" => {
            let (head, nodes) = if let [head, nodes@..] = params.as_slice() {
                (head, nodes)
            } else {
                return Err(ExpansionError::new(
                    &format!("`define` macro takes at least \
                        two (2) arguments ({} were given.", params.len()),
                    site));
            };

            // If head is atomic, we assign to a 'variable'.
            let def_macro = if let Some(variable) = head.atomic() {
                let mut definition = Macro::new(&variable.value);
                for node in nodes {
                    definition.body.push(node.clone());
                }
                definition
            } else {  // Otherwise, we are assigning to a 'function'.
                let (name, params) = if let ParseNode::List(call) = head {
                    let (name, params) = if let [name, params@..] = call.as_slice() {
                        (name, params)
                    } else {
                        return Err(ExpansionError::new(
                            "`define` function definition must at \
                             least have a name.", site));
                    };
                    let mut arguments = Vec::with_capacity(params.len());
                    for node in params {  // Verify params are symbols.
                        if let ParseNode::Symbol(param) = node {
                            arguments.push(param.value.clone());
                        } else {
                            return Err(ExpansionError::new(
                                "`define` function arguments must be \
                                 symbols/identifers.", site));
                        };
                    }
                    if let ParseNode::Symbol(name) = name {
                        (name.value.clone(), arguments)
                    } else {
                        return Err(ExpansionError::new(
                            "`define` function name must be \
                             a symbol/identifier.", site));
                    }
                } else {
                    return Err(ExpansionError::new(
                        "First argument of `define` macro must be a list \
                         or variable name/identifier.", site));
                };

                let mut definition = Macro::new(&name);
                definition.params = params;
                for node in nodes {
                    definition.body.push(node.clone());
                }
                definition
            };

            self.definitions.insert(def_macro.name.clone(), def_macro);

            Ok(vec![])
        },
        "ifdef" => {
            if params.len() < 2 || params.len() > 3 {
                eprintln!("{:?}", params);
                return Err(ExpansionError::new(&format!("`ifdef` takes one (1) \
                        condition and one (1) consequent, a third optional \
                        alternative expression may also be provided, but \
                        `ifdef` was given {} arguments.", params.len()),
                    site));
            }
            let symbol = if let Some(node) = params[0].atomic() {
                node.value
            } else {
                return Err(ExpansionError::new("The first argument to \
                    `ifdef` must be a symbol/name.", &params[0].site()));
            };

            if self.definitions.contains_key(&symbol) {
                Ok(self.expand_node(params[1].clone())?)
            } else {
                if let Some(alt) = params.get(2) {
                    Ok(self.expand_node(alt.clone())?)
                } else {
                    Ok(vec![])
                }
            }
        },
        "include" => {
            let params = self.expand_nodes(params)?;
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
            let path = Path::new(&path);
            let tree = match super::parse_file_noexpand(&path) {
                Ok(tree) => tree,
                Err(error) => {
                    let err = ExpansionError::new(
                        &format!("{}", error), site);
                    // Try with `.sex` extensions appended.
                    let mut with_ext = PathBuf::from(path);
                    let filename = path.file_name().ok_or(err.clone())?;
                    with_ext.pop();

                    let mut new_filename = OsString::new();
                    new_filename.push(filename);
                    new_filename.push(".sex");

                    with_ext.push(new_filename);
                    match super::parse_file_noexpand(&with_ext) {
                        Ok(tree) => tree,
                        Err(_)   => return Err(err)
                    }
                }
            };

            // Build new (expanded) tree, with result of previous
            // parse, while recursively expanding each branch in the
            // tree too, as they are added.
            let mut expanded_tree = Vec::with_capacity(tree.len());
            for branch in tree {
                expanded_tree.extend(self.expand_node(branch)?);
            }
            Ok(expanded_tree)
        },
        "date" => {
            let params = self.expand_nodes(params)?;
            let date_format = if let [ p ] = params.as_slice() {
                p
            } else {
                return Err(ExpansionError::new(
                    &format!("`{}' macro only expects one formatting argument.",
                             name),
                    site))
            };

            let (date_format, site) = if let Some(node) = date_format.atomic() {
                (node.value, node.site)
            } else {
                return Err(ExpansionError::new(
                    &format!("`{}' macro needs string (or atomic) \
                              formatting argument.", name),
                    site))
            };

            let now = chrono::Local::now();
            let formatted = now.format(&date_format).to_string();
            Ok(vec![ParseNode::String(Node::new(&formatted, &site))])
        },
        "log" => {
            let mut words = Vec::with_capacity(params.len());
            for param in self.expand_nodes(params)? {
                if let Some(word) = param.atomic() {
                    words.push(word.value.clone());
                } else {
                    return Err(ExpansionError::new("`log` should only take \
                        arguments that are either symbols, strings or numbers.",
                        &param.site()));
                }
            }

            eprintln!("{} {} {}: {}", "[#]".bold(), "log".bold().yellow(),
                site, words.join(" "));
            Ok(vec![])
        }
        name => {
            let params = self.expand_nodes(params)?;

            let mac = if let Some(mac) = self.definitions.get(name) {
                mac
            } else {
                return Err(ExpansionError::new(
                    &format!("Macro not found (`{}').", name), site))
            };

            // Instance of expansion subcontext.
            let mut subcontext = self.clone();
            // Check enough arguments were given.
            if params.len() != mac.params.len() {
                return Err(ExpansionError::new(
                    &format!("`%{}` macro expects {} arguments, \
                             but {} were given.", &mac.name, mac.params.len(),
                             params.len()), site));
            }
            // Define arguments for body.
            for i in 0..params.len() {
                let mut arg_macro = Macro::new(&mac.params[i]);
                arg_macro.body.push(params[i].clone());
                subcontext.definitions.insert(mac.params[i].clone(), arg_macro);
            }
            // Expand body.
            subcontext.expand_nodes(mac.body.clone())
        }
    }}

    pub fn expand_node(&mut self, node : ParseNode)
    -> Result<ParseTree, ExpansionError> {
        match node {
            ParseNode::Symbol(ref sym) => {
                // Check if symbol starts with %... and replace it
                // with it's defined value.
                if sym.value.starts_with("%") {
                    let name = &sym.value[1..];
                    if let Some(def) = self.definitions.get(name) {
                        if !def.params.is_empty() {  // Should not be a function.
                            return Err(ExpansionError::new(
                                &format!("`{}` is a macro that takes arguments, \
                                    and cannot be used as a variable.", name),
                                &sym.site))
                        }
                        Ok(def.body.clone())
                    } else {  // Not found.
                        Err(ExpansionError::new(
                            &format!("No such macro, `{}`.", name),
                            &sym.site))
                    }
                } else {
                    Ok(vec![node])
                }
            },
            ParseNode::List(list) => {
                // Check for macro invocation (%_ _ _ _).
                // Recurse over every element.
                let len = list.len();
                let mut call = list.into_iter();
                let head = call.next();

                if let Some(ParseNode::Symbol(ref sym)) = head {
                    if sym.value.starts_with("%") {
                        // Rebuild node...
                        let name = &sym.value[1..];
                        let Node { site, .. } = sym;
                        // Clean macro arguments from whitespace tokens.
                        let params = parser::strip(&call.collect(), false);
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

    fn expand_nodes(&mut self, tree : ParseTree) -> Result<ParseTree, ExpansionError> {
        let mut expanded = Vec::with_capacity(tree.len());
        for branch in tree {
            expanded.extend(self.expand_node(branch)?);
        }
        Ok(expanded)
    }
}


/// Macro-expansion phase.
/// Macros start with `%...'.
pub fn expand(tree : ParseTree) -> Result<ParseTree, ExpansionError> {
    let mut context = ExpansionContext::new();
    context.expand_nodes(tree)
}
