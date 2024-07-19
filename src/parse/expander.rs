use super::parser::{Node, ParseNode, ParseTree, Parser};
use super::tokens::Site;

use std::fmt::Display;
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

use colored::*;
use formatx;
use unicode_width::UnicodeWidthStr;

/// Error type for errors while expanding macros.
#[derive(Debug, Clone)]
pub struct ExpansionError<'a>(pub String, pub Site<'a>);

impl<'a> ExpansionError<'a> {
    /// Create a new error given the ML, the message, and the site.
    pub fn new(msg: &str, site: &Site<'a>) -> Self {
        Self(msg.to_owned(), site.to_owned())
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
/// - and its defintion (i.e. *body*).
#[derive(Debug, Clone)]
pub struct Macro<'a> {
    name: String,
    params: Box<[String]>,
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

#[derive(Debug, Clone)]
pub struct Expander<'a> {
    parser: Parser,
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

    /// Define a macro with `(%define a b)` --- `a` is a symbol or a list `(c ...)` where `c` is a symbol.
    /// macro definitions will eliminate any preceding whitespace, so make sure trailing whitespace provides
    /// the whitespace you need.
    fn expand_define_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let [head, nodes@..] = &*params else {
            return Err(ExpansionError(
                format!("`%define` macro takes at least \
                    two (2) arguments ({} were given.", params.len()),
                node.owned_site()));
        };

        // If head is atomic, we assign to a 'variable'.
        // Aditionally, we evaluate its body *eagerly*.
        let def_macro = if let Some(variable) = head.atomic() {
            let nodes = nodes.to_owned().into_boxed_slice();
            let body = self.expand_nodes(nodes)?;
            Rc::new(Macro {
                name: variable.value.clone(),
                params: Box::new([]),
                body,
            })
        } else {  // Otherwise, we are assigning to a 'function'.
            let ParseNode::List { nodes: defn_nodes, .. } = head else {
                return Err(ExpansionError(
                    "First argument of `%define` macro must be a list \
                        or variable name/identifier.".to_owned(),
                    node.site().to_owned()));
            };
            let [name, params@..] = &**defn_nodes else {
                return Err(ExpansionError(
                    "`%define` macro definition must at \
                        least have a name.".to_owned(),
                    node.site().to_owned()));
            };
            let mut arguments: Vec<String> = Vec::with_capacity(params.len());
            for param_node in params {  // Verify arguments are symbols.
                if let ParseNode::Symbol(param) = param_node {
                    arguments.push(param.value.clone());
                } else {
                    return Err(ExpansionError(
                        "`define` function arguments must be \
                            symbols/identifers.".to_owned(),
                        node.site().to_owned()));
                };
            }
            let ParseNode::Symbol(name_node) = name else {
                return Err(ExpansionError(
                    "`define` function name must be \
                        a symbol/identifier.".to_owned(),
                    node.site().to_owned()));
            };
            let name = name_node.value.clone();

            Rc::new(Macro {
                name,
                params: arguments.into_boxed_slice(),
                body: nodes.to_owned().into_boxed_slice(),
            })
        };

        self.insert_variable(def_macro.name.to_owned(), def_macro);
        Ok(Box::new([]))
    }

    /// `(%ifdef symbol a b)` --- `b` is optional, however, if not provided *and*
    /// the symbol is not defined, it will erase the whole expression, and whitespace will not
    /// be preseved before it. If that's a concern, provide `b` as the empty string `""`.
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
            // FIXME: Borrow-checker won't let me use params[0].site() as site!
            return Err(ExpansionError(
                "The first argument to `ifdef` must be a symbol/name.".to_string(),
                node.site().clone()));
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
        let include_error = |error: Box<dyn Display>| ExpansionError(
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
        let embed_error = |error: Box<dyn Display>| ExpansionError(
            format!("{}", error), site.to_owned());
        let mut value: Result<String, ExpansionError> = Err(
            embed_error(Box::new("No path tested.")));
        // Try all include directories until one is succesful.
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

    fn expand_date_macro(&self, node: &ParseNode<'a>, params: Box<[ParseNode<'a>]>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        let params = self.expand_nodes(params)?;
        let [date_format] = &*params else {
            return Err(ExpansionError::new(
                "`%date' macro only expects one formatting argument.",
                node.site()))
        };

        let Some(Node { value: date_format, .. }) = date_format.atomic() else {
            return Err(ExpansionError::new(
                "`%date' macro needs string (or atomic) \
                formatting argument.", node.site()))
        };

        let now = chrono::Local::now();
        let formatted = now.format(&date_format).to_string();
        let date_string_node = ParseNode::String(Node {
            value: formatted,
            site: node.site().clone(),
            leading_whitespace: node.leading_whitespace().to_string(),
        });
        Ok(Box::new([date_string_node]))
    }

    /// `(%log ...)` logs to `STDERR` when called and leaves *no* node behind.
    /// This means whitespace preceeding `(%log ...)` will be removed!
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
        let mut seperator = "/";  // Default namespace seperator is `/`.
        while let Some(ParseNode::Attribute { keyword, node, site, .. }) = args.peek() {
            let _ = args.next();
            match keyword.as_str() {
                "separator" => match node.atomic() {
                    Some(Node { value, .. }) => seperator = &value,
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
        // `%namespace` macro and include the defintion prefixed by
        // the namespace in the *current* scope.
        {
            let mut self_defs = self.definitions.borrow_mut();
            let defs = context.definitions.borrow();
            for (key, value) in defs.iter() {
                let new_key = format!("{}{}{}", namespace.value, seperator, key);
                self_defs.insert(new_key, value.clone());
            }
        }
        // Return remaining body of the macro.
        Ok(args.cloned().collect())
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

    fn expand_macro(&self, name: &str, node: &ParseNode<'a>, params: ParseTree<'a>)
    -> Result<ParseTree<'a>, ExpansionError<'a>> {
        // Eagerly evaluate parameters passed to macro invocation.
        let params = self.expand_nodes(params)?;

        let Some(mac) = self.get_variable(name) else {
            return Err(ExpansionError::new(
                &format!("Macro not found (`{}').", name), &node.owned_site()))
        };

        // Instance of expansion subcontext.
        let subcontext = self.create_subcontext();
        // Check enough arguments were given.
        if params.len() != mac.params.len() {
            return Err(ExpansionError(
                format!("`%{}` macro expects {} arguments, \
                        but {} were given.", &mac.name, mac.params.len(),
                        params.len()), node.site().to_owned()));
        }
        // Define arguments for body.
        for i in 0..params.len() {
            let arg_macro = Macro {
                name: mac.params[i].to_owned(),
                params: Box::new([]),
                body: Box::new([params[i].clone()]), //< Argument as evaluated at call-site.
            };
            subcontext.insert_variable(mac.params[i].to_string(), Rc::new(arg_macro));
        }
        // Expand body.
        let mut expanded = subcontext.expand_nodes(mac.body.clone())?.to_vec();
        // Inherit leading whitespace of invocation.
        if let Some(first_node) = expanded.get_mut(0) {
            first_node.set_leading_whitespace(node.leading_whitespace().to_owned());
        }
        Ok(expanded.into_boxed_slice())
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
            "ifdef"     => self.expand_ifdef_macro(node, params),
            "raw"       => self.expand_raw_macro(node, params),
            "string"    => self.expand_string_macro(node, params),
            "include"   => self.expand_include_macro(node, params),
            "embed"     => self.expand_embed_macro(node, params),
            "namespace" => self.expand_namespace_macro(node, params),
            "date"      => self.expand_date_macro(node, params),
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
                        Ok(def.body.clone())
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
                let head = call.next();

                // Pathway: (%_ _ _) macro invocation.
                if let Some(ref symbol@ParseNode::Symbol(..)) = head {
                    let node = self.register_invocation(node.clone());
                    let name = symbol.atomic().unwrap().value.clone();
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
                expanded_list.extend(self.expand_node(head.unwrap().clone())?);
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
