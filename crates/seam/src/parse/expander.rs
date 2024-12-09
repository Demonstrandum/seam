use super::parser::{Node, ParseNode, ParseTree, Parser};
use super::tokens::Site;

use std::{
    fmt,
    cell::RefCell,
    path::PathBuf,
    ffi::OsString,
    error::Error,
    rc::Rc,
    collections::{
        HashMap,
        BTreeSet,
    },
};

use chrono::TimeZone;
use colored::*;
use fixed;
use formatx;
use glob::glob;
use unicode_width::UnicodeWidthStr;
use markdown;

// proc macros for generating macros.
use seam_argparse_proc_macro::arguments;

/// Error type for errors while expanding macros.
#[derive(Debug, Clone)]
pub struct ExpansionError<'a>(pub String, pub Site<'a>);

impl<'a> ExpansionError<'a> {
    /// Create a new error given the ML, the message, and the site.
    pub fn new<S: Into<String>>(msg: S, site: &Site<'a>) -> Self {
        Self(msg.into(), site.to_owned())
    }
}

/// Implement fmt::Display for user-facing error output.
impl<'a> fmt::Display for ExpansionError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ExpansionError(msg, site) = self;
        let line_prefix = format!("  {} |", site.line);
        let line_view = site.line_slice();
        writeln!(f, "{} {}", line_prefix, line_view)?;
        writeln!(f, "{:>prefix_offset$} {:~>text_offset$}{:^>length$}", "|", "", "",
            prefix_offset=UnicodeWidthStr::width(line_prefix.as_str()),
            text_offset=site.line_column() - 1,
            length=site.width())?;
        write!(f, "[{}] Error Expanding Macro {}: {}",
            "**".red().bold(), site, msg)
    }
}

/// Implements std::error::Error for macro expansion error.
impl<'a> Error for ExpansionError<'a> { }

/// A macro consists of:
/// - its name;
/// - its argument list (if any);
/// - and its definition (i.e. *body*).
#[derive(Debug, Clone)]
pub struct Macro<'a> {
    #[allow(dead_code)]
    name: String,
    params: Box<[ParseNode<'a>]>,
    body: Box<[ParseNode<'a>]>
}
// TODO: Macro to also store its own scope (at place of definition)
// in order to implement lexical scoping.

impl<'a> Macro<'a> {
    pub fn new(name: &str) -> Macro {
        Macro {
            name: name.to_string(),
            params: Box::new([]),
            body:   Box::new([]),
        }
    }
}

/// Type of variable scope owned by an `Expander` instance.
pub type Scope<'a> = RefCell<HashMap<String, Rc<Macro<'a>>>>; // Can you believe this type?

/// Macro expansion context, takes a parser and expands
/// any macro calls found in the generated parse-tree.
#[derive(Debug, Clone)]
pub struct Expander<'a> {
    parser: Parser,
    /// Include directories, in order of search.
    includes: BTreeSet<PathBuf>,
    subparsers: RefCell<Vec<Parser>>,
    subcontexts: RefCell<Vec<Self>>,
    invocations: RefCell<Vec<ParseNode<'a>>>,
    definitions: Scope<'a>,
}

impl<'a> Expander<'a> {
    pub fn new(parser: Parser) -> Self {
        Self {
            parser,
            includes: BTreeSet::from([PathBuf::from(".")]),
            subparsers: RefCell::new(Vec::new()),
            subcontexts: RefCell::new(Vec::new()),
            invocations: RefCell::new(Vec::new()),
            definitions: RefCell::new(HashMap::new()),
        }
    }

    /// Get underlying source-code of the active parser for current unit.
    pub fn get_source(&self) -> &str {
        self.parser.get_source()
    }

    /// Supply additional include-directories for the macros
    /// to use when searching for files to include/emebed.
    /// Files are searched for in the order that of the directories.
    pub fn add_includes<T: Iterator>(&mut self, dirs: T)
        where T::Item: Into<PathBuf>
    {
        for dir in dirs {
            self.includes.insert(dir.into());
        }
    }

    /// Add a subparser owned by the expander context.
    fn register_parser(&self, parser: Parser) -> &'a Parser {
        {
            let mut parsers = self.subparsers.borrow_mut();
            parsers.push(parser);
        }
        self.latest_parser().unwrap()
    }

    /// Get the latest subparser added.
    fn latest_parser(&self) -> Option<&'a Parser> {
        let p = self.subparsers.as_ptr();
        unsafe { (*p).last() }
    }

    /// Create and register a subcontext built from the current context.
    fn create_subcontext(&self) -> &mut Self {
        {
            let copy = self.clone();
            let mut contexts = self.subcontexts.borrow_mut();
            contexts.push(copy);
        }
        self.latest_context().unwrap()
    }

    /// Delete a subcontext from the current context.
    fn remove_subcontext(&self) -> () {
        let mut contexts = self.subcontexts.borrow_mut();
        contexts.pop();
    }

    /// Get the latest subparser added.
    fn latest_context(&self) -> Option<&mut Self> {
        let contexts = self.subcontexts.as_ptr();
        unsafe { (*contexts).last_mut() }
    }

    fn register_invocation(&self, node: ParseNode<'a>) -> &ParseNode<'a> {
        let invocations = self.invocations.as_ptr();
        unsafe {
            (*invocations).push(node);
            (*invocations).last().unwrap()
        }
    }

    /// Update variable (macro) for this scope.
    fn insert_variable(&self, name: String, var: Rc<Macro<'a>>) {
        let mut defs = self.definitions.borrow_mut();
        defs.insert(name, var);
    }

    /// Check if macro exists in this scope.
    fn has_variable(&self, name: &str) -> bool {
        let defs = self.definitions.borrow();
        defs.contains_key(name)
    }

    fn get_variable(&self, name: &str) -> Option<Rc<Macro<'a>>> {
        self.definitions.borrow().get(name).map(|m| m.clone())
    }

    /// Pattern-matching variable bind for two nodes (the pattern and the value).
    fn bind(&self, pattern: &ParseNode<'a>, value: &ParseNode<'a>)
    -> Result<(), ExpansionError<'a>> {
        match pattern {
            // Bind :named argument.
            ParseNode::Attribute { keyword: k0, node: node0, .. } => match value {
                ParseNode::Attribute { keyword: k1, node: node1, .. } => if k0 == k1 {
                    self.bind(node0, node1)
                } else {
                    Err(ExpansionError(
                        format!("Mismatch named argument, looking for :{}, found :{}.", k0, k1),
                        value.owned_site(),
                    ))
                },
                _ => Err(ExpansionError(
                    format!("Looking for named argument :{}, got {} instead.", k0, value.node_type()),
                    value.owned_site(),
                )),
            },
            // Bind a list containing &-rest syntax and :named arguments.
            ParseNode::List { nodes: nodes0, .. } => match value {
                ParseNode::List { nodes: nodes1, .. } => self.bind_list(value, nodes0, nodes1),
                _ => Err(ExpansionError(
                    format!("Cannot assign {} to a list.", value.node_type()),
                    value.owned_site(),
                ))
            },
            // Symbols are simply assigned as variable names.
            ParseNode::Symbol(symbol) => {
                self.insert_variable(symbol.value.clone(), Rc::new(Macro {
                    name: symbol.value.clone(),
                    params: Box::new([]),
                    body: Box::new([ value.clone() ]),
                }));
                Ok(())
            },
            // Other literals must match exactly and no assignment takes place.
            ParseNode::Number(number0) => match value {
                ParseNode::Number(number1) => if number0 == number1 { Ok(()) } else {
                    Err(ExpansionError(
                        format!("Expected the number {} here, got the number {} instead.",
                            number0.value, number1.value),
                        number1.site.to_owned(),
                    ))
                },
                _ => Err(ExpansionError(
                    format!("Expected a number here, got {} instead.", value.node_type()),
                    value.owned_site(),
                )),
            },
            ParseNode::String(string0) | ParseNode::Raw(string0) => match value {
                ParseNode::String(string1) | ParseNode::Raw(string1) => if string0 == string1 { Ok(()) } else {
                    Err(ExpansionError(
                        format!("Expected the string {:?} here, got the string {:?} instead.",
                            string0.value, string1.value),
                        string1.site.to_owned(),
                    ))
                },
                _ => Err(ExpansionError(
                    format!("Expected a string here, got {} instead.", value.node_type()),
                    value.owned_site(),
                )),
            }
        }
    }

    fn bind_list(&self, assigned: &ParseNode<'a>, nodes0: &ParseTree<'a>, nodes1: &ParseTree<'a>)
    -> Result<(), ExpansionError<'a>> {
        let mut rest_node = None;
        let mut rest_kw_node = None;
        let mut rhs_index: usize = 0;
        let mut expected: usize = 0;
        let mut rhs_named = HashMap::new(); // Contains keyword -> attribute node.
        let mut lhs_named = HashMap::new(); // Contains keyword -> attr. value node (defaults).
        // We loop this way (not a for loop) so we can control
        // when exactly we advance to the next LHS node, potentially
        // doing multiple iterations on the same node.
        let mut nodes0_iter = nodes0.iter();
        let mut maybe_node0 = nodes0_iter.next();
        while let Some(node0) = maybe_node0 {
            // Named arguments (attributes) can appear out of order.
            // We'll remember them from later.
            if let ParseNode::Attribute { keyword, node, .. } = node0 {
                lhs_named.insert(keyword, node);
                // A named argument in the LHS does not mean we saw one in the RHS,
                // so we continue and do not increment rhs_index.
                maybe_node0 = nodes0_iter.next();
                continue;
            }
            // Check for &&-rest keyword matching syntax.
            let found_kw_rest = node0.symbol().map(|name| name.value.starts_with("&&")).unwrap_or(false);
            if found_kw_rest {
                // If another &&-rest node has been found, report an error.
                if rest_kw_node.is_some() {
                    return Err(ExpansionError::new(
                        "Found multiple nodes matching named argument &&-rest syntax.",
                        node0.site(),
                    ));
                }
                // Otherwise, make note of the node it corresponds to.
                rest_kw_node = Some(node0);
                // Note that we don't increment the `rhs_index`,
                // since a &&rest node does not match the corresponding item in the RHS.
                maybe_node0 = nodes0_iter.next();
                continue;
            }
            // Check for &-rest regular argument matching syntax.
            let found_rest = node0.symbol().map(|name| name.value.starts_with('&')).unwrap_or(false);
            if found_rest {
                // If another &-rest node has been found, report an error.
                if rest_node.is_some() {
                    return Err(ExpansionError::new(
                        "Found multiple nodes matching &-rest syntax.",
                        node0.site(),
                    ));
                }
                // Otherwise, make note of the node it corresponds to.
                rest_node = Some(node0);
                // Note that we don't increment the `rhs_index`,
                // since a &rest node does not match the corresponding item in the RHS.
                maybe_node0 = nodes0_iter.next();
                continue;
            }
            // Assign matched node unless the RHS has too few nodes.
            if rhs_index >= nodes1.len() {
                return Err(ExpansionError(
                    format!("Too few values given, looking for value {} out of only {}.", rhs_index + 1, nodes1.len()),
                    assigned.owned_site(),
                ));
            }
            let node1 = &nodes1[rhs_index];
            if let ParseNode::Attribute { keyword, .. } = node1 {
                // This is a named argument given in the RSH, so it does not correspond to
                // the specific non-named argument in the LHS, so we keep looking until we
                // get to it, and remember all the named arguments we find along the way.
                rhs_named.insert(keyword.clone(), node1);
                rhs_index += 1;
                // Continue without advancing to the next LHS `node0`.
                continue;
            }
            self.bind(node0, node1)?;
            maybe_node0 = nodes0_iter.next();
            expected += 1;
            rhs_index += 1;
        }
        // Assign any remaining arguments in the RHS to &rest.
        let mut rest = vec![];
        while rhs_index < nodes1.len() {
            let node1 = &nodes1[rhs_index];
            if let ParseNode::Attribute { keyword, .. } = node1 {
                // There might be remaining named argument further down the RHS list.
                rhs_named.insert(keyword.clone(), node1);
            } else {
                rest.push(node1.clone());
            }
            rhs_index += 1;
        }
        // Now, whether the &rest argument was given or not...
        if let Some(rest_node) = rest_node {
            // Assign the &rest variable to a list containing the extra nodes.
            let rest_symbol = rest_node.symbol().unwrap();
            let rest_name = rest_symbol.value[1..].to_owned();
            self.insert_variable(
                rest_name.to_owned(),
                Rc::new(Macro {
                    name: rest_name,
                    params: Box::new([]),
                    body: rest.into_boxed_slice(),
                }),
            );
        } else if let Some(last_excess_node) = rest.last() {
            // No &rest node mentioned, but excess arguments collected? That's an error.
            let got = expected + rest.len();
            return Err(ExpansionError(
                format!("Excess number of arguments, expected {}, got {}.", expected, got),
                last_excess_node.owned_site(),
            ));
        }
        // Assign all the named arguments.
        for (keyword, default) in lhs_named.iter() {
            // Remove memory of assigned node from RHS.
            let value = match rhs_named.remove(*keyword) {
                // Found the named argument in the RHS, so don't use the default.
                Some(attr) => attr.attribute().unwrap().1,
                // No named corresponding argument in the RHS means we have to use its default.
                None => default,
            };
            // Bind it to a symbol with the same name as the keyword.
            self.insert_variable(
                (*keyword).to_owned(),
                Rc::new(Macro {
                    name: (*keyword).to_owned(),
                    params: Box::new([]),
                    body: Box::new([ *value.clone() ]),
                }),
            );
        }
        // Capture remaining named arguments under the &&-macro.
        if let Some(rest_kw_node) = rest_kw_node {
            let rest_kw_symbol = rest_kw_node.symbol().unwrap();
            let rest_kw_name = &rest_kw_symbol.value[2..];
            // Collect the named arguments.
            let attrs: Vec<String> = rhs_named.keys().cloned().collect();
            let mut nodes = Vec::with_capacity(attrs.len());
            for attr in attrs {
                let named = rhs_named.remove(&attr).unwrap();
                nodes.push(named.clone());
            }
            // Insert the &&-variable.
            self.insert_variable(rest_kw_name.to_string(), Rc::new(Macro {
                name: rest_kw_name.to_string(),
                params: Box::new([]),
                body: nodes.into_boxed_slice(),
            }));
        }
        // Any remaining RHS named nodes not covered by the LHS, are excess/errors.
        if !rhs_named.is_empty() {
            // Go through RHS named nodes and list all the excess/invalid names.
            let mut excess_keywords: Vec<&str> = vec![];
            let mut rhs = rhs_named.iter();
            let (keyword, some_node) = rhs.next().unwrap(); // Non-empty.
            excess_keywords.push(keyword);
            for (keyword, _) in rhs {
                excess_keywords.push(keyword.as_ref());
            }
            let excess_keywords: Vec<String> = excess_keywords
                .iter()
                .map(|kw| format!("`:{}`", kw))
                .collect();
            let known_keywords: Vec<String> = lhs_named
                .iter()
                .map(|(kw, _)| format!("`:{}`", kw))
                .collect();
            let excess_keywords = excess_keywords.join(", ");
            if known_keywords.is_empty() {
                return Err(ExpansionError(
                    format!(
                        "This macro does not expect any keyword arguments, however the following were provided: {}",
                        excess_keywords,
                    ),
                    some_node.owned_site(),
                ));
            }
            let known_keywords = known_keywords.join(", ");
            return Err(ExpansionError(
                format!(concat!(
                        "Unknown excess keywords provided: {};",
                        " expected keyword arguments are: {}."
                    ),
                    excess_keywords,
                    known_keywords,
                ),
                some_node.owned_site(),
            ));
        }
        Ok(())
    }

    /// `%(match expr (pattrern1 body1) (pattern2 body2) ...)`
    fn expand_match_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let (expr, patterns)  = match &*params {
            [expr, patterns@..] => (expr, patterns),
            _ => return Err(ExpansionError::new(
                "Match syntax is: `(%match expr [...(pattern value)])`.",
                node.site(),
            )),
        };
        let [expr,] = &*self.expand_node(expr.clone())? else {
            return Err(ExpansionError::new(
                "Value to match against must be single value.",
                expr.site(),
            ));
        };
        for pattern in patterns {
            let Some(pattern_list) = pattern.list() else {
                return Err(ExpansionError::new(
                    "Pattern in `%match` must be a list `(pattern ...value)`.",
                    pattern.site(),
                ));
            };
            let [pattern, value@..] = &**pattern_list else {
                return Err(ExpansionError::new(
                    "Empty pattern not allowed in `%match`.",
                    pattern.site(),
                ));
            };
            let [pattern,] = &*self.expand_node(pattern.clone())? else {
                return Err(ExpansionError::new(
                    "Pattern must evaluate to a single node.",
                    pattern.site(),
                ));
            };
            // Now attempt to `bind` against pattern, successful binds means
            // we evaluate the RHS of the list and return that.
            let subcontext = self.clone(); // Subscope.
            if let Ok(()) = subcontext.bind(pattern, expr) {
                return subcontext.expand_nodes(value.into());
            }
        }

        // No match means no nodes are produced.
        Ok(Box::new([]))
    }

    /// Define a macro with `(%define a b)` --- `a` is a symbol or a list `(c ...)` where `c` is a symbol.
    /// macro definitions will eliminate any preceding whitespace, so make sure trailing whitespace provides
    /// the whitespace you need.
    fn expand_define_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let [head, nodes@..] = &*params else {
            return Err(ExpansionError(
                format!("`%define` macro takes at least \
                    two (2) arguments, while {} were given.", params.len()),
                node.owned_site()));
        };

        // If head is atomic, we assign to a 'variable'.
        // Additionally, we evaluate its body *eagerly*.
        let (name, arguments, body): (String, Vec<ParseNode<'a>>, ParseTree)
        = if let Some(variable) = head.symbol() {
            let nodes = nodes.to_owned().into_boxed_slice();
            let body = self.expand_nodes(nodes)?;
            (variable.value.clone(), vec![], body)
        } else {  // Otherwise, we are assigning to a 'function'.
            let ParseNode::List { nodes: defn_nodes, .. } = head else {
                return Err(ExpansionError(
                    "First argument of `%define` macro must be a list \
                        or variable name/identifier.".to_owned(),
                    head.site().to_owned()));
            };
            let [name, params@..] = &**defn_nodes else {
                return Err(ExpansionError(
                    "`%define` macro definition must at \
                        least have a name.".to_owned(),
                    head.site().to_owned()));
            };
            let arguments: Vec<ParseNode<'a>> = params.to_vec();
            let ParseNode::Symbol(name_node) = name else {
                return Err(ExpansionError(
                    "`define` function name must be \
                        a symbol/identifier.".to_owned(),
                    name.site().to_owned()));
            };
            let name = name_node.value.clone();

            let body = nodes.to_owned().into_boxed_slice();
            (name, arguments, body)
        };

        self.create_macro(name, arguments, body)?;
        Ok(Box::new([]))
    }

    /// `(%ifdef symbol a b)` --- `b` is optional, however, if not provided *and*
    /// the symbol is not defined, it will erase the whole expression, and whitespace will not
    /// be preserved before it. If that's a concern, provide `b` as the empty string `""`.
    fn expand_ifdef_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        if params.len() < 2 || params.len() > 3 {
            return Err(ExpansionError(format!("`ifdef` takes one (1) \
                    condition and one (1) consequent, a third optional \
                    alternative expression may also be provided, but \
                    `ifdef` was given {} arguments.", params.len()),
                node.site().to_owned()));
        }
        let symbol = if let Some(node) = params[0].atomic() {
            node.value.to_owned()
        } else {
            return Err(ExpansionError(
                "The first argument to `ifdef` must be a symbol/name.".to_string(),
                params[0].owned_site()));
        };

        let mut expanded = if self.has_variable(&symbol) {
            self.expand_node(params[1].clone())?
        } else {
            if let Some(alt) = params.get(2) {
                self.expand_node(alt.clone())?
            } else {
                Box::new([])
            }
        };
        if let Some(first_node) = expanded.get_mut(0) {
            first_node.set_leading_whitespace(node.leading_whitespace().to_owned());
        }
        Ok(expanded)
    }

    fn expand_do_macro(&self, _node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        self.expand_nodes(params)
    }

    fn expand_include_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params: Box<[ParseNode<'a>]> = self.expand_nodes(params)?;
        let [path_node] = &*params else {
            return Err(ExpansionError(
                format!("Incorrect number of arguments \
                    to `%include' macro. Got {}, expected {}.",
                    params.len(), 1),
                node.site().to_owned()));
        };

        let Some(Node { value: path, site, .. }) = path_node.atomic()  else {
            return Err(ExpansionError(
                "Bad argument to `%include' macro.\n\
                    Expected a path, but did not get any value
                    that could be interpreted as a path.".to_string(),
                path_node.site().to_owned()))
        };

        // Open file, and parse contents!
        let include_error = |error: Box<dyn fmt::Display>| ExpansionError(
            format!("{}", error), site.to_owned());
        let mut parser: Result<Parser, ExpansionError> = Err(
            include_error(Box::new("No path tested.")));
        // Try all include directories until one is succesful.
        for include_dir in &self.includes {
            let path = include_dir.join(path);
            parser = super::parser_for_file(&path)
                .or_else(|err| {
                    let err = Box::new(err);
                    // Try with `.sex` extensions appended.
                    let mut with_ext = PathBuf::from(&path);
                    let filename = path.file_name()
                        .ok_or(include_error(err))?;
                    with_ext.pop();  // Remove old filename.
                    // Build new filename with `.sex` appended.
                    let mut new_filename = OsString::new();
                    new_filename.push(filename);
                    new_filename.push(".sex");
                    with_ext.push(new_filename); // Replace with new filename.
                    match super::parser_for_file(&with_ext) {
                        Ok(parser) => Ok(parser),
                        Err(err)   => Err(include_error(Box::new(err)))
                    }
                });
            if parser.is_ok() { break; }
        }
        // Register the parser for the found file.
        let parser = self.register_parser(parser?);
        let tree = match parser.parse() {
            Ok(tree) => tree,
            Err(error) => return Err(ExpansionError(
                format!("{}", error), node.site().to_owned()))
        };

        // Build new (expanded) tree, with result of previous
        // parse, while recursively expanding each branch in the
        // tree too, as they are added.
        let mut expanded_tree = Vec::with_capacity(tree.len());
        for branch in tree {
            expanded_tree.extend(self.expand_node(branch)?);
        }
        // First node should inherit leading whitespace from (%include ...) list.
        if expanded_tree.len() != 0 {
            expanded_tree[0].set_leading_whitespace(node.leading_whitespace().to_owned());
        }
        Ok(expanded_tree.into_boxed_slice())
    }

    fn expand_embed_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params: Box<[ParseNode<'a>]> = self.expand_nodes(params)?;
        let [path_node] = &*params else {
            return Err(ExpansionError(
                format!("Incorrect number of arguments \
                    to `%embed' macro. Got {}, expected {}.",
                    params.len(), 1),
                node.site().to_owned()));
        };

        let Some(Node { value: path, site, .. }) = path_node.atomic()  else {
            return Err(ExpansionError(
                "Bad argument to `%embed' macro.\n\
                    Expected a path, but did not get any value
                    that could be interpreted as a path.".to_string(),
                path_node.site().to_owned()))
        };

        // Open file, and read contents!
        let embed_error = |error: Box<dyn fmt::Display>| ExpansionError(
            format!("{}", error), site.to_owned());
        let mut value: Result<String, ExpansionError> = Err(
            embed_error(Box::new("No path tested.")));
        // Try all include directories until one is successful.
        for include_dir in &self.includes {
            let path = include_dir.join(path);
            value = std::fs::read_to_string(path)
                .map_err(|err| embed_error(Box::new(err)));
            if value.is_ok() { break; }
        }
        let value = value?;
        Ok(Box::new([
            ParseNode::String(Node {
                value,
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            }),
        ]))
    }

    /// The `(%markdown ...)` macro parses both the fenced `--- ... ---` metadata at the
    /// top of the file (which it expands to `%define`s), and converts the rest of the
    /// markdown file into a raw-string containing the converted plain HTML.
    fn expand_markdown_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): string,
            optional("only"): literal["frontmatter", "content"],
            optional("separator"): literal,
        }?;
        // Parse the makdown content only, the frontmatter only, or do both.
        #[derive(Clone, Copy, PartialEq, Eq)]
        enum Only { Frontmatter, Content, Both }
        // Extract arguments and options.
        let contents = args.number.1.value;
        let only = args.only.map_or(Only::Both, |option| match option.value.as_ref() {
            "frontmatter" => Only::Frontmatter,
            "content" => Only::Content,
            _ => unreachable!(),
        });
        // Default to using the '/' namespace separator for frontmatter definitions.
        let sep = args.separator.map_or(String::from("/"), |sep| sep.value);
        // Live dangerously / trust the author:
        let danger = markdown::CompileOptions {
          allow_dangerous_html: true,
          allow_dangerous_protocol: true,
          ..markdown::CompileOptions::default()
        };
        // Flavour options:
        let flavour = markdown::ParseOptions {
            gfm_strikethrough_single_tilde: false,
            math_text_single_dollar: true,
            constructs: markdown::Constructs {
                frontmatter: true,
                gfm_table: true,
                gfm_task_list_item: true,
                ..markdown::Constructs::default()
            },
            ..markdown::ParseOptions::default()
        };
        // Options.
        let options = markdown::Options { parse: flavour, compile: danger, };

        // How to convert to HTML.
        let to_html = | | -> Result<ParseTree, _> {
            // Convert to HTML.
            let html = match markdown::to_html_with_options(contents.as_ref(), &options) {
                Ok(html) => html,
                Err(err) => return Err(ExpansionError(
                    format!("Failed to render markdown: {}", err),
                    args.number.1.site.to_owned(),
                ))
            };
            // Return the raw html.
            Ok(Box::new([
                ParseNode::Raw(Node {
                    value: html,
                    site: node.owned_site(),
                    leading_whitespace: node.leading_whitespace().to_owned(),
                }),
            ]))
        };

        // How to extract front-matter.
        let extract_frontmatter = | | -> Result<(), _> {
            use markdown::mdast;
            let ast = match markdown::to_mdast(contents.as_ref(), &options.parse) {
                Ok(ast) => ast,
                Err(err) => return Err(ExpansionError(
                    format!("Failed to render markdown: {}", err),
                    args.number.1.site.to_owned(),
                ))
            };
            let mdast::Node::Root(root) = ast else { unreachable!() };
            let root = root.children;
            let root: &[mdast::Node] = root.as_ref();
            match root {
                [mdast::Node::Yaml(mdast::Yaml { value: yaml, .. }), ..] => {
                    // Parse the YAML and convert it into macro definitions.
                    let _ = expand_yaml(self, yaml, &sep, node.site())?;
                    Ok(())
                },
                [mdast::Node::Toml(mdast::Toml { value: toml, .. }), ..] => {
                    // Parse the TOML and convert it into macro definitions.
                    let _ = expand_toml(self, toml, &sep, node.site())?;
                    Ok(())
                },
                _ => return Err(ExpansionError::new(
                    "This markdown does not contain any frontmatter.",
                    &args.number.1.site,
                ))
            }
        };

        match only {
            Only::Frontmatter => {
                extract_frontmatter()?;
                Ok(Box::new([]))
            },
            Only::Content => to_html(),
            Only::Both => {
                // Ignore any errors if no frontmatter exists.
                let _ = extract_frontmatter();
                to_html()
            },
        }
    }

    fn expand_yaml_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): string,
            optional("separator"): literal,
        }?;
        let yaml = args.number.1.value;
        let sep = args.separator.map_or(String::from("/"), |sep| sep.value);

        expand_yaml(self, &yaml, &sep, node.site())
    }

    fn expand_toml_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): string,
            optional("separator"): literal,
        }?;
        let yaml = args.number.1.value;
        let sep = args.separator.map_or(String::from("/"), |sep| sep.value);

        expand_toml(self, &yaml, &sep, node.site())
    }

    fn expand_get_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): literal,
            mandatory(2): any,
            optional("separator"): literal,
        }?;
        let sep = args.separator.map_or(String::from("/"), |sep| sep.value);
        let path = args.number.1.value.split(&sep);

        let mut view;
        let mut node = args.number.2;
        for item in path {
            // Verify the current node is a list so it can be indexed.
            if let Some(list) = node.list() {
                view = list.to_vec();
            } else {
                return Err(ExpansionError(
                    format!("Cannot `%get' on {} node.",node.node_type()),
                    node.owned_site(),
                ))
            }
            let mut got = Err(ExpansionError(
                format!("Could not find attribute with keyword `:{}`.", item),
                node.owned_site(),
            ));
            if let Ok(index) = item.parse::<usize>()  {
                // Try to find n-th element of `view`.
                got = view.get(index).map(|node| node.clone()).ok_or(ExpansionError(
                    format!("Index {} is out of bounds in list of length {}.", index, view.len()),
                    node.owned_site(),
                ));
            }
            if got.is_err() {
                // Try to find :item attribute in list.
                for node in view.iter() {
                    if let ParseNode::Attribute { keyword, node, .. } = node {
                        if item == keyword {
                            got = Ok(*node.clone());
                            break;
                        }
                    }
                }
            }
            node = got?;
        }

        Ok(Box::new([node]))
    }

    fn expand_date_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?;
        let (_, args) = arguments! { [&params]
            mandatory(1): literal,
            optional(2): number,
            optional("timezone"): number,
        }?;
        let timezone_offset: i32 = match args.timezone {
            Some(ref offset) => match offset.value.parse::<fixed::types::I32F32>() {
                Ok(offset) => (offset * 60 * 60).round().to_num(),
                Err(_) => return Err(ExpansionError::new(
                    "Invalid (decimal) timezone offset in hours.",
                    &offset.site,
                )),
            },
            None => chrono::Local::now().offset().local_minus_utc(),
        };
        let date_format = args.number.1.value;
        let time = if let Some(time) = args.number.2 {
            let Ok(secs) = time.value.parse::<i64>() else {
                return Err(ExpansionError::new(
                    "Timestamp not a valid UNIX epoch signed integer.",
                    &time.site,
                ));
            };
            match chrono::DateTime::from_timestamp(secs, 0) {
                Some(time) => time,
                None => return Err(ExpansionError::new("Invalid timestamp.", &time.site)),
            }
        } else {
            chrono::Utc::now()
        };

        let Some(timezone) = chrono::FixedOffset::east_opt(timezone_offset) else {
            return Err(ExpansionError(
                format!("Failed to compute UTC+(east) offset of {} seconds", timezone_offset),
                args.timezone.map_or(node.owned_site(), |node| node.site),
            ));
        };
        let time = time.with_timezone(&timezone);
        let formatted = time.format(&date_format).to_string();
        let date_string_node = ParseNode::String(Node {
            value: formatted,
            site: node.site().clone(),
            leading_whitespace: node.leading_whitespace().to_string(),
        });
        Ok(Box::new([date_string_node]))
    }

    fn expand_timestamp_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?;
        let (_, args) = arguments! { [&params]
            mandatory(1): literal,
            mandatory(2): literal,
            optional("timezone"): number,
        }?;
        let format = args.number.1.value;
        let date_string = args.number.2.value;

        let timezone_offset: i32 = match args.timezone {
            Some(ref offset) => match offset.value.parse::<fixed::types::I32F32>() {
                Ok(offset) => (offset * 60 * 60).round().to_num(),
                Err(_) => return Err(ExpansionError::new(
                    "Invalid (decimal) timezone offset in hours.",
                    &offset.site,
                )),
            },
            None => chrono::Local::now().offset().local_minus_utc(),
        };

        let Some(timezone) = chrono::FixedOffset::east_opt(timezone_offset) else {
            return Err(ExpansionError(
                format!("Failed to compute UTC+(east) offset of {} seconds", timezone_offset),
                args.timezone.map_or(node.owned_site(), |node| node.site),
            ));
        };

        let timestamp = if let Ok(datetime) = chrono::DateTime::parse_from_str(&date_string, &format) {
            // Timezone information already given. Ignore any `:timezone` attribute.
            datetime.timestamp()
        } else {
            // Parse NaiveDateTime instead and get timzone from attribute, or default to local time.
            let datetime = match chrono::NaiveDateTime::parse_from_str(&date_string, &format) {
                Ok(datetime) => datetime,
                Err(err) => return Err(ExpansionError(
                    format!("Failed to parse date: {}", err),
                    node.owned_site(),
                )),
            };
            let datetime = timezone.from_local_datetime(&datetime);
            let datetime = match datetime.earliest() {
                Some(local) => local,
                None => return Err(ExpansionError::new(
                    "Timezone: local time falls in a gap in local time.",
                    node.site(),
                ))
            };
            datetime.timestamp()
        };

        Ok(Box::new([
            ParseNode::Number(Node {
                value: format!("{}", timestamp),
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            })
        ]))
    }

    /// `(%log ...)` logs to `STDERR` when called and leaves *no* node behind.
    /// This means whitespace preceding `(%log ...)` will be removed!
    fn expand_log_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let mut words = Vec::with_capacity(params.len());
        for param in self.expand_nodes(params)? {
            if let Some(word) = param.atomic() {
                words.push(word.value.clone());
            } else {
                return Err(ExpansionError::new("`log` should only take \
                    arguments that are either symbols, strings or numbers.",
                    node.site()));
            }
        }

        eprintln!("{} {} {}: {}", "[#]".bold(), "log".bold().yellow(),
            node.site(), words.join(" "));
        Ok(Box::new([]))
    }

    fn expand_os_env_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?;
        let [ref var] = *params else {
            return Err(ExpansionError::new(
                "`%os/env' expects excatly one argument.",
                node.site()));
        };
        let Some(var) = var.atomic() else {
            return Err(ExpansionError::new(
                "`%os/env' argument must be atomic (not a list).",
                var.site()));
        };
        let Node { site, leading_whitespace, .. } = var.clone();
        let Ok(value) = std::env::var(&var.value) else {
            return Err(ExpansionError(
                format!("No such environment variable ($`{}') visible.", &var.value),
                site));
        };
        Ok(Box::new([
            ParseNode::String(Node { value, site, leading_whitespace }),
        ]))
    }

    fn expand_format_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?;
        let [format_str, ..] = &*params else {
            return Err(ExpansionError::new(
                "`%format' expects at a format-string.",
                node.site()));
        };
        let ParseNode::String(format_str) = format_str else {
            return Err(ExpansionError::new(
                "First argument to `%format' must be a string.",
                format_str.site()));
        };
        // Iterate and collect format arguments.
        let mut arguments = params.iter();
        let _ = arguments.next();  // Skip the format-string.
        let Ok(mut template) = formatx::Template::new(&format_str.value) else {
            return Err(ExpansionError::new(
                "Invalid format string.",
                &format_str.site));
        };
        for mut var in arguments {
            // Check if we're replacing a named or positional placeholder.
            let mut named: Option<&str> = None;
            if let ParseNode::Attribute { keyword, node, .. } = var {
                named = Some(keyword.as_str());
                var = node;
            }
            // TODO: Somehow let non-atomic values be formattable?
            let Some(Node { value, .. }) = var.atomic() else {
                return Err(ExpansionError(
                    format!("In `%format', the compound {} type is not formattable.",
                        var.node_type()),
                    var.site().clone()));
            };
            // Replace the placeholder.
            match named {
                Some(name) => template.replace(name, value),
                None       => template.replace_positional(value),
            }
        }
        // Template has been constructed, so now attempt to do subsitituions and
        // render the formatted string.
        match template.text() {
            Ok(value) => Ok(Box::new([
                ParseNode::String(Node {
                    value,
                    site: node.owned_site(),
                    leading_whitespace: node.leading_whitespace().to_owned(),
                })
            ])),
            Err(err) => Err(ExpansionError(
                format!("Failed to format string: {}", err.message()),
                format_str.site.clone()))
        }
    }

    fn expand_namespace_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        // Start evaluating all the arguments to the macro in a separate context.
        let context = self.clone();
        let params =  context.expand_nodes(params)?;
        let mut args = params.iter().peekable();
        let Some(namespace) = args.next().and_then(ParseNode::atomic) else {
            return Err(ExpansionError::new("Expected a namespace name.", node.site()));
        };
        // Parse options to macro.
        let mut separator = "/";  // Default namespace separator is `/`.
        while let Some(ParseNode::Attribute { keyword, node, site, .. }) = args.peek() {
            let _ = args.next();
            match keyword.as_str() {
                "separator" => match node.atomic() {
                    Some(Node { value, .. }) => separator = &value,
                    None => return Err(ExpansionError(
                        format!("`%namespace' separator must be a symbol, got a {}.", node.node_type()),
                        node.owned_site())),
                },
                opt => return Err(ExpansionError(
                    format!("Unknown option `:{}' to `%namespace' macro.", opt),
                    site.clone())),
            }
        }
        // Find all the definitions made within the context of the
        // `%namespace` macro and include the definition prefixed by
        // the namespace in the *current* scope.
        {
            let mut self_defs = self.definitions.borrow_mut();
            let defs = context.definitions.borrow();
            for (key, value) in defs.iter() {
                let new_key = format!("{}{}{}", namespace.value, separator, key);
                self_defs.insert(new_key, value.clone());
            }
        }
        // Return remaining body of the macro.
        Ok(args.cloned().collect())
    }

    fn expand_for_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let (_parser, args) = arguments! { [&params]
            mandatory(1): any,
            mandatory(2): symbol["in"],
            mandatory(3): list,
            rest: any,
        }?;
        let it = args.number.1;
        let list = args.number.3;
        let list = self.expand_nodes(list.into_boxed_slice())?;
        let body = args.rest.into_boxed_slice();

        let context = self.clone();
        let mut expanded = Vec::with_capacity(list.len());
        for item in list {
            context.bind(&it, &item)?;
            let evaluated = context.expand_nodes(body.clone())?;
            expanded.extend(evaluated);
        }

        Ok(expanded.into_boxed_slice())
    }

    fn expand_glob_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): literal,
            optional("type"): literal["file", "directory", "any"],
            optional("sort"): literal["modified", "created", "name", "type", "none"],
            optional("order"): literal["ascending", "descending"],
        }?;

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum PathTypes { File, Dir, Any }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum SortBy { Modified, Created, Name, Type, None }
        // Default to both files and dirs.
        let path_types = args.r#type.map(|typ| match typ.value.as_ref() {
            "file" => PathTypes::File,
            "directory" => PathTypes::Dir,
            "any" => PathTypes::Any,
            _ => unreachable!(),
        }).unwrap_or(PathTypes::Any);
        // Default to no ordering.
        let sortby = args.sort.map(|typ| match typ.value.as_ref() {
            "modified" => SortBy::Modified,
            "created" => SortBy::Created,
            "name" => SortBy::Name,
            "type" => SortBy::Type,
            "none" => SortBy::None,
            _ => unreachable!(),
        }).unwrap_or(SortBy::None);
        // Default to ascending order.
        let is_ascending_order = args.order.map_or(true, |node| node.value == "ascending");

        let pattern: &str = args.number.1.value.as_ref();
        let paths = match glob(pattern) {
            Ok(paths) => paths,
            Err(err) => return Err(ExpansionError(
                format!("Failed to read glob pattern: {}", err),
                args.number.1.site.to_owned(),
            )),
        };

        struct GlobPath<'a> {
            node: ParseNode<'a>,
            meta: std::fs::Metadata,
            path: PathBuf,
            sortby: SortBy,
        }
        impl<'a> PartialEq for GlobPath<'a> {
            fn eq(&self, other: &Self) -> bool {
                self.path == other.path
            }
        }
        impl<'a> Eq for GlobPath<'a> { }
        impl<'a> PartialOrd for GlobPath<'a> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                if self.sortby != other.sortby { return None };
                let sortby = self.sortby;
                match sortby {
                    SortBy::Created => {
                        let Ok(d0) = self.meta.created() else { return Some(std::cmp::Ordering::Less) };
                        let Ok(d1) = other.meta.created() else { return Some(std::cmp::Ordering::Less) };
                        if d0 == d1 { // If created at the same time, default to alphabetical.
                            self.path.partial_cmp(&other.path)
                        } else {
                            // "ascending" order should be in terms of age.
                            d0.partial_cmp(&d1).map(|ord| ord.reverse()) // New < Old
                        }
                    },
                    SortBy::Modified => {
                        let Ok(d0) = self.meta.modified() else { return Some(std::cmp::Ordering::Less) };
                        let Ok(d1) = other.meta.modified() else { return Some(std::cmp::Ordering::Less) };
                        if d0 == d1 { // If modified at the same time, default to alphabetical.
                            self.path.partial_cmp(&other.path)
                        } else {
                            // "ascending" order should be in terms of recentness.
                            d0.partial_cmp(&d1).map(|ord| ord.reverse()) // New < Old
                        }
                    },
                    SortBy::Name => self.path.partial_cmp(&other.path),
                    SortBy::Type => {
                        // First sort by file vs. dir.
                        if self.meta.is_dir() && other.meta.is_file() {
                            Some(std::cmp::Ordering::Less) // Folder < File
                        } else if self.meta.is_file() && other.meta.is_dir() {
                            Some(std::cmp::Ordering::Greater) // File > Folder
                        } else if let Some(ext) = self.path.extension() {
                            if let Some(other_ext) = other.path.extension() {
                                if ext == other_ext {
                                    self.path.partial_cmp(&other.path) // Sort by name when extension are the same.
                                } else {
                                    ext.partial_cmp(other_ext) // Sort by different file extensions before name.
                                }
                            } else {
                                Some(std::cmp::Ordering::Greater) // With ext. > No ext.
                            }
                        } else {
                            if let Some(_) = other.path.extension() {
                                Some(std::cmp::Ordering::Less) // No ext. < With ext.
                            } else {
                                self.path.partial_cmp(&other.path) // Sort by name when neither have extensions.
                            }
                        }
                    }
                    SortBy::None => Some(std::cmp::Ordering::Less),
                }
            }
        }
        impl<'a> Ord for GlobPath<'a> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                assert_eq!(self.sortby, other.sortby);
                self.partial_cmp(other).unwrap()
            }
        }

        // Collect paths.
        let mut collection: std::collections::BTreeSet<GlobPath> = Default::default();
        for path in paths {
            let path = match path {
                Ok(path) => path,
                Err(err) => return Err(ExpansionError(
                    format!("glob failed: {}", err),
                    args.number.1.site.to_owned(),
                )),
            };
            let meta = std::fs::metadata(&path).unwrap();
            match path_types {
                PathTypes::File if !meta.is_file() => continue,
                PathTypes::Dir  if !meta.is_dir()  => continue,
                _ => {},
            }
            let node = ParseNode::String(Node {
                value: path.to_string_lossy().to_string(),
                site: args.number.1.site.to_owned(),
                leading_whitespace: String::from(" "),
            });
            collection.insert(GlobPath { node, meta, path, sortby });
        }
        let mut expanded = if is_ascending_order {
            collection.into_iter().map(|path| path.node).collect::<ParseTree>()
        } else {
            collection.into_iter().rev().map(|path| path.node).collect::<ParseTree>()
        };
        if let Some(first) = expanded.first_mut() {
            first.set_leading_whitespace(String::new());
        }
        Ok(expanded)
    }

    fn expand_raw_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let mut builder = String::new();
        let args = self.expand_nodes(params)?;
        for arg in args {
            let Some(Node { value, leading_whitespace, .. }) = arg.atomic() else {
                return Err(ExpansionError(
                    format!("Expected a literal, found a {} node instead.", arg.node_type()),
                    arg.owned_site()));
            };
            builder += leading_whitespace;
            builder += value;
        }
        Ok(Box::new([
            ParseNode::Raw(Node {
                value: builder,
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            })
        ]))
    }

    fn expand_string_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let mut builder = String::new();
        let args = self.expand_nodes(params)?;
        for arg in args {
            let Some(Node { value, leading_whitespace, .. }) = arg.atomic() else {
                return Err(ExpansionError(
                    format!("Expected a literal, found a {} node instead.", arg.node_type()),
                    arg.owned_site()));
            };
            builder += leading_whitespace;
            builder += value;
        }
        Ok(Box::new([
            ParseNode::String(Node {
                value: builder,
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            })
        ]))
    }

    fn expand_reverse_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): list,
        }?;
        let list = args.number.1;
        let mut reversed = Vec::with_capacity(list.len());

        for i in 0..list.len() {
            let mut item = list[list.len() - i - 1].clone();
            item.set_leading_whitespace(list[i].leading_whitespace().to_owned());
            reversed.push(item);
        }

        let ParseNode::List { site, end_token, leading_whitespace, .. }
            = params[0].clone() else { unreachable!() };
        Ok(Box::new([
            ParseNode::List {
                nodes: reversed.into_boxed_slice(),
                site,
                end_token,
                leading_whitespace
            }
        ]))
    }

    fn expand_sort_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): any,
            optional("order"): literal["ascending", "descending"],
            optional("key"): symbol,
        }?;

        let call_node = node;
        let key_fn_site = args.key.clone().map_or(call_node.owned_site(), |key_fn| key_fn.site);
        let key_fn = args.key.map_or(String::from("do"), |key| key.value);
        let ascending = args.order.map_or(true, |order| order.value == "ascending");

        /// Keeps track of nodes and the key by which to sort them by.
        struct SortItem<'b> {
            node: ParseNode<'b>,
            key: String,
        }

        let ParseNode::List { nodes, site, end_token, .. } = args.number.1 else {
            return Err(ExpansionError(
                format!("`%sort` expects a list, was given {}.", args.number.1.node_type()),
                args.number.1.owned_site(),
            ))
        };

        let mut items = Vec::with_capacity(nodes.len());
        let mut whitespace = Vec::with_capacity(nodes.len()); // Preserve whitespace order.
        for node in nodes {
            let key = match self.expand_invocation(&key_fn, call_node, Box::new([node.clone()])) {
                Ok(key) => key,
                Err(err) => return Err(ExpansionError(
                    format!("Error evaluating `:key` macro:\n{}", err),
                    key_fn_site,
                ))
            };
            if key.len() > 1 {
                return Err(ExpansionError(
                    format!("`:key` macro expanded to more than one value (namely {} values).", key.len()),
                    key_fn_site,
                ));
            } else if key.len() != 1 {
                return Err(ExpansionError::new(
                    "`:key` macro did not yield any value to compare against.",
                    &key_fn_site,
                ));
            }

            let key = key[0].clone();
            let key_type = key.node_type();
            let key_site = key.owned_site();
            let Some(key) = key.into_atomic() else {
                return Err(ExpansionError(
                    format!("List items in `%sort` must resolve to literals under `:key`; got {} instead.", key_type),
                    key_site,
                ));
            };
            let key = key.value;
            whitespace.push(node.leading_whitespace().to_owned());
            items.push(SortItem { node, key });
        }
        // Whitespace is reversed so .pop() removes the first item.
        whitespace.reverse();
        // Sort by the evaluated .key string.
        items.sort_by(|item0, item1| {
            let (item0, item1) = if ascending { (item0, item1) } else { (item1, item0) };
            // First try to compare as integers, failing that, as floats, and then strings.
            if let (Ok(n0), Ok(n1)) = (item0.key.parse::<i64>(), item1.key.parse::<i64>()) {
                return n0.cmp(&n1)
            }
            if let (Ok(f0), Ok(f1)) = (item0.key.parse::<f64>(), item1.key.parse::<f64>()) {
                if let Some(ord) = f0.partial_cmp(&f1) {
                    return ord;
                }
            }
            item0.key.cmp(&item1.key)
        });
        // Extract nodes and amend whitespace.
        let nodes = items.into_iter().map(|item| {
            let mut node = item.node;
            node.set_leading_whitespace(whitespace.pop().unwrap());
            node
        }).collect();

        Ok(Box::new([
            ParseNode::List {
                nodes,
                site,
                end_token,
                leading_whitespace: node.leading_whitespace().to_owned(),
            }
        ]))
    }

    fn expand_join_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): literal,
            optional("trailing"): literal["true", "false"],
            rest: literal,
        }?;

        let sep = &args.number.1.value;
        let trailing = args.trailing.map(|n| n.value == "true").unwrap_or(false);
        let items: Vec<&str> = args.rest.iter().map(|n| n.value.as_str()).collect();
        let joined = items.join(sep) + if trailing { sep } else { "" };
        Ok(Box::new([
            ParseNode::String(Node {
                value: joined,
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            })
        ]))
    }

    fn expand_concat_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            rest: literal,
        }?;

        let joined: String = args.rest.iter().fold
            (String::new(),
            |acc, x| acc + x.value.as_ref()
        );

        Ok(Box::new([
            ParseNode::String(Node {
                value: joined,
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            })
        ]))
    }

    fn expand_map_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_, args) = arguments! { [&params]
            mandatory(1): symbol,
            rest: any,
        }?;

        let mut expanded = vec![];
        for arg in args.rest {
            expanded.extend(self.expand_invocation(args.number.1.value.as_ref(), node, Box::new([arg]))?);
        }
        Ok(expanded.into_boxed_slice())
    }

    /// Filters all null nodes (`()`-nodes) out of the list.
    fn expand_filter_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_, args) = arguments! { [&params]
            mandatory(1): symbol,
            rest: any,
        }?;

        let mut expanded = vec![];
        for arg in args.rest {
            let nodes = self.expand_invocation(args.number.1.value.as_ref(), node, Box::new([arg]))?;
            match &*nodes {
                [node,] if node.null() => {},
                _ => expanded.extend(nodes),
            };
        }
        Ok(expanded.into_boxed_slice())
    }

    fn expand_splat_macro(&self, _node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let mut expanded = vec![];
        for param in params {
            if let ParseNode::List { nodes, leading_whitespace, ..} = param {
                let mut nodes = nodes.to_vec();
                if let [first, ..] = nodes.as_mut_slice() {
                    first.set_leading_whitespace(leading_whitespace);
                }
                expanded.extend(nodes);
            } else {
                expanded.push(param.clone());
            }
        }
        Ok(expanded.into_boxed_slice())
    }

    fn expand_list_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let ParseNode::List { site, end_token, leading_whitespace, .. } = node else {
            panic!("expand macro call given non-list call node.");
        };
        Ok(Box::new([
            ParseNode::List {
                nodes: params,
                site: site.to_owned(),
                end_token: end_token.to_owned(),
                leading_whitespace: leading_whitespace.to_owned(),
            }
        ]))
    }

    fn expand_strip_macro(&self, _node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let mut params = self.expand_nodes(params)?; // Eager.
        if let Some(first) = params.get_mut(0) {
            first.set_leading_whitespace(String::new());
        }
        Ok(params)
    }

    fn expand_apply_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?; // Eager.
        let (_parser, args) = arguments! { [&params]
            mandatory(1): symbol,
            rest: any,
        }?;

        self.expand_invocation(args.number.1.value.as_ref(), node, args.rest.into_boxed_slice())
    }

    fn expand_lambda_macro(&self, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let (_parser, args) = arguments! { [&params]
            mandatory(1): any,
            rest: any,
        }?;

        let head: ParseNode<'a> = args.number.1;
        let arglist = match head.list() {
            Some(list) => list.to_vec(),
            None => match head.symbol() {
                Some(_) => vec![head.clone()],
                None => Err(ExpansionError::new(
                    "Expected argument(s) as symbol or list of arguments.",
                    head.site(),
                ))?
            }
        };

        let name = format!("__lambda{}", node.site().uuid());

        self.create_macro(name.clone(), arglist, args.rest.into_boxed_slice())?;

        Ok(Box::new([
            ParseNode::Symbol(Node {
                value: name,
                site: node.owned_site(),
                leading_whitespace: node.leading_whitespace().to_owned(),
            })
        ]))
    }

    fn create_macro(&self, name: String, arglist: Vec<ParseNode<'a>>, body: ParseTree<'a>)
    -> Result<Rc<Macro<'a>>, ExpansionError<'a>> {
        // Check excess &-macros and &&-macros are not present.
        let rest_params: Vec<&ParseNode> = arglist.iter()
            .filter(|node| node.symbol().map(
                |name| name.value.starts_with('&') && !name.value.starts_with("&&"))
            .unwrap_or(false))
            .collect();
        match rest_params.as_slice() {
            [_, excess, ..] => return Err(ExpansionError::new(
                "Excess `&`-variadic argument capture variables.",
                excess.site()
            )),
            _ => {}
        };
        let kw_rest_params: Vec<&ParseNode> = arglist.iter()
            .filter(|node| node.symbol().map(|name| name.value.starts_with("&&")).unwrap_or(false))
            .collect();
        match kw_rest_params.as_slice() {
            [_, excess, ..] => return Err(ExpansionError::new(
                "Excess `&&`-variadic named argument capture variables.",
                excess.site()
            )),
            _ => {}
        };

        // Create and insert macro.
        let mac = Rc::new(Macro {
            name: name.clone(),
            params: arglist.into_boxed_slice(),
            body,
        });
        self.insert_variable(name, mac.clone());
        Ok(mac)
    }

    fn apply_macro(&self, mac: Rc<Macro<'a>>, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        // Instance of expansion subcontext.
        let subcontext = self.create_subcontext();
        // Construct fake list of arguments and parameters and pattern match on them.
        subcontext.bind_list(node, &mac.params, &params)?;
        // Expand body.
        let expanded = subcontext.expand_nodes(mac.body.clone())?.to_vec();
        // Finished expanding macro, delete the subcontext.
        self.remove_subcontext();
        // Return the body of the evaluated macro.
        Ok(expanded.into_boxed_slice())
    }

    fn expand_macro(&self, name: &str, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        // Eagerly evaluate parameters passed to macro invocation.
        let params = self.expand_nodes(params)?;

        let Some(mac) = self.get_variable(name) else {
            return Err(ExpansionError::new(
                &format!("Macro not found (`{}').", name), &node.owned_site()))
        };

        self.apply_macro(mac, node, params)
    }

    fn expand_invocation(&self,
                         name: &str, //< Name of macro (e.g. %define).
                         node: &ParseNode<'a>, //< Node for `%'-macro invocation.
                         params: Box<[ParseNode<'a>]> //< Passed in arguments.
    ) -> Result<ParseTree<'a>, ExpansionError<'a>> {
        // Some macros are lazy (e.g. `ifdef`), so each macro has to
        //   expand the macros in its arguments individually.
        match name {
            "define"    => self.expand_define_macro(node, params),
            "match"     => self.expand_match_macro(node, params),
            "ifdef"     => self.expand_ifdef_macro(node, params),
            "do"        => self.expand_do_macro(node, params),
            "get"       => self.expand_get_macro(node, params),
            "raw"       => self.expand_raw_macro(node, params),
            "string"    => self.expand_string_macro(node, params),
            "include"   => self.expand_include_macro(node, params),
            "embed"     => self.expand_embed_macro(node, params),
            "namespace" => self.expand_namespace_macro(node, params),
            "markdown"  => self.expand_markdown_macro(node, params),
            "yaml"      => self.expand_yaml_macro(node, params),
            "json"      => self.expand_yaml_macro(node, params),
            "toml"      => self.expand_toml_macro(node, params),
            "glob"      => self.expand_glob_macro(node, params),
            "for"       => self.expand_for_macro(node, params),
            "sort"      => self.expand_sort_macro(node, params),
            "reverse"   => self.expand_reverse_macro(node, params),
            "date"      => self.expand_date_macro(node, params),
            "timestamp" => self.expand_timestamp_macro(node, params),
            "join"      => self.expand_join_macro(node, params),
            "concat"    => self.expand_concat_macro(node, params),
            "map"       => self.expand_map_macro(node, params),
            "filter"    => self.expand_filter_macro(node, params),
            "splat"     => self.expand_splat_macro(node, params),
            "list"      => self.expand_list_macro(node, params),
            "strip"     => self.expand_strip_macro(node, params),
            "apply"     => self.expand_apply_macro(node, params),
            "lambda"    => self.expand_lambda_macro(node, params),
            "log"       => self.expand_log_macro(node, params),
            "format"    => self.expand_format_macro(node, params),
            "os/env"    => self.expand_os_env_macro(node, params),
            _           => self.expand_macro(name, node, params),
        }
    }

    pub fn expand_node(&self, node: ParseNode<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        match node {
            ParseNode::Symbol(ref sym) => {
                // Check if symbol starts with %... and replace it
                // with it's defined value.
                if sym.value.starts_with("%") {
                    let name = &sym.value[1..];
                    if let Some(def) = self.get_variable(name) {
                        if !def.params.is_empty() {  // Should not be a function.
                            return Err(ExpansionError::new(
                                &format!("`{}` is a macro that takes arguments, \
                                    and cannot be used as a variable.", name),
                                &sym.site))
                        }
                        let mut expanded = def.body.clone();
                        // Inherit the whitespace of the call-site.
                        if let Some(first) = expanded.first_mut() {
                            first.set_leading_whitespace(sym.leading_whitespace.to_owned());
                        }
                        Ok(expanded)
                    } else {  // Not found.
                        Err(ExpansionError(
                            format!("No such macro, `{}`.", name),
                            sym.site.to_owned()))
                    }
                } else {
                    Ok(Box::new([node]))
                }
            },
            ParseNode::List { ref nodes, ref site, ref end_token, ref leading_whitespace } => {
                // Check for macro invocation (%_ _ _ _).
                // Recurse over every element.
                let len = nodes.len();
                let mut call = nodes.to_vec().into_iter();
                let Some(head) = call.next() else {
                    return Ok(Box::new([node]));
                };

                // Pathway: (%_ _ _) macro invocation.
                if let Some(symbol) = head.symbol() {
                    let node = self.register_invocation(node.clone());
                    let name = symbol.value.clone();
                    if name.starts_with("%") {
                        // Rebuild node...
                        let name = &name[1..];
                        let mut params: Vec<ParseNode> = call.collect();
                        // Delete leading whitespace of leading argument.
                        if let Some(leading) = params.first_mut() {
                            if !leading.leading_whitespace().contains('\n') {
                                leading.set_leading_whitespace(String::from(""));
                            }
                        }
                        return self.expand_invocation(name, node, params.into_boxed_slice());
                    }
                }
                // Otherwise, if not a macro, just expand child nodes incase they are macros.
                let mut expanded_list = Vec::with_capacity(len);
                expanded_list.extend(self.expand_node(head.clone())?);
                for elem in call {
                    expanded_list.extend(self.expand_node(elem)?);
                }

                Ok(Box::new([ParseNode::List {
                    nodes: expanded_list.into_boxed_slice(),
                    site: site.clone(),
                    end_token: end_token.clone(),
                    leading_whitespace: leading_whitespace.clone(),
                }]))
            },
            ParseNode::Attribute { keyword, node, site, leading_whitespace } => {
                let mut expanded_nodes = self.expand_node(*node)?;
                let new_node = Box::new(expanded_nodes[0].clone());
                expanded_nodes[0] = ParseNode::Attribute {
                    keyword: keyword.clone(),
                    node: new_node,
                    site: site.clone(),
                    leading_whitespace: leading_whitespace.clone(),
                };
                Ok(expanded_nodes)
            },
            _ => Ok(Box::new([node]))
        }
    }

    pub fn expand_nodes(&self, tree: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let mut expanded = Vec::with_capacity(tree.len());
        for branch in tree {
            expanded.extend(self.expand_node(branch)?);
        }
        Ok(expanded.into_boxed_slice())
    }

    pub fn expand(&'a self) -> Result<ParseTree<'a>, Box<dyn 'a + std::error::Error>> {
        let tree = self.parser.parse()?;
        let expanded = self.expand_nodes(tree)?;
        Ok(expanded)
    }
}

/// For example, the YAML below,
/// ```yaml
/// a: 2
/// b: hello
/// nested:
///     hello: world
///     array:
///     - aa: 0
///       bb: 1
///     - aa: 2
///       bb: 3
/// ```
/// evaluates to the following variables:
/// ```text
/// (%yaml "...") #=> (:a 2 :b hello (:hello world :array ((:aa 0 :bb 1) (:aa 2 :bb 3)))))
/// a #=> 2
/// b #=> "hello"
/// nested #=> (:hello world :array ((:aa 0 :bb 1) (:aa 2 :bb 3)))
/// nested/hello #=> world
/// nested/array #=> ((:aa 0 :bb 1) (:aa 2 :bb 3))
/// nested/array/0 #=> (:aa 0 :bb 1)
/// nested/array/1 #=> (:aa 2 :bb 3)
/// nested/array/0/aa #=> 0
/// nested/array/0/bb #=> 1
/// nested/array/1/aa #=> 2
/// nested/array/1/bb #=> 3
/// ```
fn expand_yaml<'a>(context: &Expander<'a>, text: &str, sep: &str, site: &Site<'a>) -> Result<ParseTree<'a>, ExpansionError<'a>> {
    use yaml_rust2 as yaml;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Mode { Map, Seq, }

    struct EventSink<'a, 'b> {
        /// The macro expansion context.
        context: &'b Expander<'a>,
        /// A variable name if the YAML parser is currently parsing
        /// the assignment of an item in a map.
        defining: Option<String>,
        /// The collection of nodes which eventually get assigned
        /// to a `ParseNode::List` after a map or array is parsed.
        nodes: Vec<ParseNode<'a>>,
        parent: Vec<Vec<ParseNode<'a>>>,
        /// The sequence of qualifiers for a nested name definition.
        prefix: Vec<String>,
        /// The namespace separator (e.g. `/` or `.`).
        sep: String,
        /// Whether we're parsing a map or a sequence (array).
        mode: Option<Mode>,
        modes: Vec<Mode>,
        /// The site of the original YAML-parsing macro.
        site: Site<'a>,
    }

    impl<'a, 'b> EventSink<'a, 'b> {
        fn qualified(&self, name: &str) -> String {
            if self.prefix.is_empty() {
                name.to_owned()
            } else {
                let prefix = self.prefix.join(&self.sep);
                format!("{}{}{}", prefix, self.sep, name)
            }
        }
    }

    impl<'a, 'b> yaml::parser::EventReceiver for EventSink<'a, 'b> {
        fn on_event(&mut self, event: yaml::Event) {
            let the_dreaded_rparen = crate::parse::tokens::Token::new(
                crate::parse::tokens::Kind::RParen,
                ")", "", self.site.clone()
            );
            match event {
                // Either defining a new variable or setting a variable to a string.
                yaml::Event::Scalar(ref value, ..) => {
                    let mut string = ParseNode::String(Node {
                        value: value.clone(),
                        site: self.site.clone(),
                        leading_whitespace: String::from(" "),
                    });
                    match self.defining {
                        Some(ref name) => {
                            // Define a variable under `name` with `value`.
                            let qualified_name = self.qualified(name);
                            self.context.insert_variable(qualified_name.clone(), Rc::new(Macro {
                                name: qualified_name,
                                params: Box::new([]),
                                body: Box::new([string.clone()]),
                            }));
                            match self.mode {
                                Some(Mode::Map) => {
                                    // Wait for next name.
                                    let keyword = name.clone();
                                    // Push keyword attribute.
                                    let attr = ParseNode::Attribute {
                                        keyword,
                                        node: Box::new(string),
                                        site: self.site.clone(),
                                        leading_whitespace: String::from(if self.nodes.is_empty() {
                                            ""
                                        } else {
                                            " "
                                        }),
                                    };
                                    self.nodes.push(attr);
                                    self.defining = None;
                                },
                                Some(Mode::Seq) => {
                                    // Push list item.
                                    if self.nodes.is_empty() {
                                        string.set_leading_whitespace(String::new());
                                    }
                                    self.nodes.push(string);
                                    self.defining = Some(format!("{}", self.nodes.len()));
                                },
                                None => panic!("cannot be defining an item outside of a map or sequence.")
                            }
                        },
                        None => match self.mode {
                            // Otherwise, we are defining a new variable under this name.
                            Some(Mode::Map) => self.defining = Some(value.clone()),
                            Some(Mode::Seq) => panic!("seq is always defining something."),
                            None => {
                                // Push item.
                                if self.nodes.is_empty() {
                                    string.set_leading_whitespace(String::new());
                                }
                                self.nodes.push(string);
                            },
                        }
                    }
                },
                // Start parsing a YAML map.
                yaml::Event::MappingStart(..) => {
                    if let Some(ref defining) = self.defining {
                        self.prefix.push(defining.clone());
                    }
                    self.defining = None;
                    self.parent.push(self.nodes.clone());
                    self.nodes = Vec::new();
                    if let Some(mode) = self.mode {
                        self.modes.push(mode);
                    }
                    self.mode = Some(Mode::Map);
                },
                // Start parsing a YAML sequence.
                yaml::Event::SequenceStart(..) => {
                    if let Some(ref defining) = self.defining {
                        self.prefix.push(defining.clone());
                    }
                    self.defining = Some(String::from("0"));
                    self.parent.push(self.nodes.clone());
                    self.nodes = Vec::new();
                    if let Some(mode) = self.mode {
                        self.modes.push(mode);
                    }
                    self.mode = Some(Mode::Seq);
                },
                // Assign the built-up map or sequence.
                yaml::Event::MappingEnd | yaml::Event::SequenceEnd => {
                    self.mode = self.modes.pop(); // Revert to previous mode.
                    let nodes = self.nodes.clone(); // Nodes in the list.
                    self.nodes = self.parent.pop().unwrap_or(Vec::new()); // Regain previous collection of nodes.
                    self.defining = match self.mode {
                        Some(Mode::Seq) => Some(format!("{}", self.nodes.len() + 1)),
                        Some(Mode::Map) | None => None
                    };
                    let name = self.prefix.pop(); // The name of this map or sequence.
                    // Construct a `ParseNode::List` containing the collected nodes.
                    let list = ParseNode::List {
                        nodes: nodes.into_boxed_slice(),
                        site: self.site.clone(),
                        end_token: the_dreaded_rparen,
                        leading_whitespace: String::from(if self.nodes.is_empty() {
                            ""
                        } else {
                            " "
                        }),
                    };
                    // Handle inserting map/seq list under a qualified variable into the context.
                    match name {
                        Some(ref name) => {
                            let name = self.qualified(name);
                            self.context.insert_variable(name.clone(), Rc::new(Macro {
                                name,
                                params: Box::new([]),
                                body: Box::new([list.clone()]),
                            }));
                        },
                        None => {},
                    };
                    // Handle growing the current nodes with the map/seq.
                    self.nodes.push(match self.mode {
                        Some(Mode::Map) => {
                            let leading_whitespace = list.leading_whitespace().to_owned();
                            let mut list = list;
                            list.set_leading_whitespace(String::from(" "));
                            ParseNode::Attribute {
                                keyword: name.clone().expect("must always be defining during a map context."),
                                node: Box::new(list),
                                site: self.site.clone(),
                                leading_whitespace,
                            }
                        },
                        Some(Mode::Seq) | None => list,
                    });
                },
                _ => {},
            }
        }
    }

    let mut sink = EventSink {
        context,
        defining: None,
        prefix: Vec::new(),
        sep: sep.to_string(),
        mode: None,
        modes: Vec::new(),
        nodes: Vec::new(),
        parent: Vec::new(),
        site: site.clone(),
    };

    yaml::parser::Parser::new_from_str(text)
        .load(&mut sink, false)
        .map_err(|err| ExpansionError(
            format!("Failed to parse YAML: {}", err),
            site.to_owned()
        ))?;

    Ok(sink.nodes.into_boxed_slice())
}

/// See [`expand_yaml`], but for the TOML configuration language instead.
fn expand_toml<'a>(context: &Expander<'a>, text: &str, sep: &str, site: &Site<'a>) -> Result<ParseTree<'a>, ExpansionError<'a>> {
    use toml;

    let table: toml::Table = text.parse()
        .map_err(|err| ExpansionError(
            format!("Failed to parse TOML: {}", err),
            site.to_owned()
        ))?;

    struct Traverser<'a, 'b> {
        context: &'b Expander<'a>,
        site: Site<'a>,
        sep: String,
        prefix: Vec<String>,
        the_dreaded_rparen: crate::parse::tokens::Token<'a>,
    }

    fn whitespace(leading: bool) -> String {
        if leading { String::new() } else { String::from(" ") }
    }

    impl<'a, 'b> Traverser<'a, 'b> {
        fn qualified(&self, name: &str) -> String {
            if self.prefix.is_empty() {
                name.to_owned()
            } else {
                let prefix = self.prefix.join(&self.sep);
                format!("{}{}{}", prefix, self.sep, name)
            }
        }

        fn define(&self, name: String, node: ParseNode<'a>) {
            let qualified = self.qualified(&name);
            self.context.insert_variable(qualified, Rc::new(Macro {
                name,
                params: Box::new([]),
                body: Box::new([node]),
            }));
        }

        fn traverse_value(&mut self, value: toml::Value, leading: bool) -> ParseNode<'a> {
            match value {
                toml::Value::Array(array) => self.traverse_array(array, leading),
                toml::Value::Table(table) => self.traverse_table(table, leading),
                toml::Value::String(string) => ParseNode::String(Node {
                    value: string,
                    site: self.site,
                    leading_whitespace: whitespace(leading),
                }),
                toml::Value::Integer(int) => ParseNode::Number(Node {
                    value: format!("{}", int),
                    site: self.site,
                    leading_whitespace: whitespace(leading),
                }),
                toml::Value::Float(float) => ParseNode::Number(Node {
                    value: format!("{}", float),
                    site: self.site,
                    leading_whitespace: whitespace(leading),
                }),
                toml::Value::Datetime(date) => ParseNode::Symbol(Node {
                    value: format!("{}", date),
                    site: self.site,
                    leading_whitespace: whitespace(leading),
                }),
                toml::Value::Boolean(boolean) => ParseNode::Symbol(Node {
                    value: format!("{}", boolean),
                    site: self.site,
                    leading_whitespace: whitespace(leading),
                }),
            }
        }

        fn traverse_array(&mut self, array: Vec<toml::Value>, leading: bool) -> ParseNode<'a> {
            let mut first = true;
            let mut expanded = vec![];
            let mut i = 0;
            for value in array {
                let name = format!("{}", i);
                self.prefix.push(name.clone());
                let node = self.traverse_value(value, first);
                self.prefix.pop();
                self.define(name, node.clone());
                expanded.push(node);
                first = false;
                i += 1;
            }
            ParseNode::List {
                nodes: expanded.into_boxed_slice(),
                site: self.site,
                end_token: self.the_dreaded_rparen,
                leading_whitespace: whitespace(leading)
            }
        }

        fn traverse_table(&mut self, table: toml::Table, leading: bool) -> ParseNode<'a> {
            let mut nodes = vec![];
            let mut first = true;
            for (keyword, value) in table {
                self.prefix.push(keyword.clone());
                let node = self.traverse_value(value, false);
                self.prefix.pop();
                self.define(keyword.clone(), node.clone());
                nodes.push(ParseNode::Attribute {
                    keyword,
                    node: Box::new(node),
                    site: self.site,
                    leading_whitespace: whitespace(first),
                });
                first = false;
            }
            let nodes = nodes.into_boxed_slice();
            ParseNode::List {
                nodes,
                site: self.site,
                end_token: self.the_dreaded_rparen,
                leading_whitespace: whitespace(leading)
            }
        }
    }

    Ok(Box::new([
        Traverser {
            context,
            site: *site,
            prefix: Vec::new(),
            sep: sep.to_owned(),
            the_dreaded_rparen: crate::parse::tokens::Token::new(
                crate::parse::tokens::Kind::RParen,
                ")", "", *site
            ),
        }.traverse_table(table, true)
    ]))
}
