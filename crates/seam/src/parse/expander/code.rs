//! Macros for working with code as data: quasiquotation, inspecting and
//! building nodes, functions over lists, walking trees, and tools for
//! writing macros.

use super::{Definition, Expander, ExpansionError, list_items, list_node, truthy, bool_node, number_node, without_leading, spaced};
use crate::parse::lexer::Lexer;
use crate::parse::parser::{Node, ParseNode, ParseTree, Parser};

type Expansion<'a> = Result<ParseTree<'a>, ExpansionError<'a>>;

fn error<'a>(message: impl Into<String>, node: &ParseNode<'a>) -> ExpansionError<'a> {
    ExpansionError::new(message, node.site())
}

fn symbol_node<'a>(call: &ParseNode<'a>, value: impl Into<std::borrow::Cow<'a, str>>) -> ParseNode<'a> {
    ParseNode::Symbol(Node::new(value, call.site(), call.leading_whitespace().clone()))
}

/// The macro a list calls, `name` for `(%name ...)`.
fn called<'n>(node: &'n ParseNode) -> Option<&'n str> {
    node.list()?.first()?.symbol()?.macro_name()
}

/// The single node a macro's argument expanded to.
fn single<'a>(nodes: ParseTree<'a>, what: &str, node: &ParseNode<'a>) -> Result<ParseNode<'a>, ExpansionError<'a>> {
    match <Box<[_; 1]>>::try_from(nodes) {
        Ok(single) => { let [single] = *single; Ok(single) },
        Err(nodes) => Err(error(format!("{what} must be a single value, but got {} values.", nodes.len()), node)),
    }
}

/// The nodes of a list argument.
fn list_of<'a>(argument: &ParseNode<'a>, call: &ParseNode<'a>, what: &str) -> Result<Vec<ParseNode<'a>>, ExpansionError<'a>> {
    match argument {
        ParseNode::List { nodes, .. } => Ok(nodes.items().collect()),
        other => Err(error(format!("{what} must be a list, but got a {}.", other.node_type()), call)),
    }
}

impl<'a> Expander<'a> {
    /// Call a function (a macro's name, as `%lambda` gives) with arguments.
    fn call(&self, function: &ParseNode<'a>, node: &ParseNode<'a>, arguments: &[ParseNode<'a>]) -> Expansion<'a> {
        let Some(name) = function.symbol() else {
            return Err(error(format!("Expected a macro (its name, or a `%lambda`), but got a {}.",
                function.node_type()), function));
        };
        self.expand_invocation(&name.value, node, arguments)
    }

    /// Call a function and give its result as one node: the node itself,
    /// or a list of the nodes it gave if not exactly one.
    fn call_one(&self, function: &ParseNode<'a>, node: &ParseNode<'a>, arguments: &[ParseNode<'a>]) -> Result<ParseNode<'a>, ExpansionError<'a>> {
        let mut result = self.call(function, node, arguments)?.into_vec();
        Ok(if result.len() == 1 { result.swap_remove(0) } else { list_node(node, spaced(result)) })
    }

    /// `(%quasi code...)` gives its code unexpanded, except for
    /// `(%unquote x)`, which is replaced by what `x` expands to, and
    /// `(%splice xs)`, which is replaced by the items of the list `xs`.
    pub(super) fn expand_quasi_macro(&self, _node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let mut out = Vec::with_capacity(params.len());
        for param in params {
            self.quasi(param, 0, &mut out)?;
        }
        Ok(out.into_boxed_slice())
    }

    /// Quasiquote a node `depth` levels within nested `%quasi`s.
    fn quasi(&self, node: &ParseNode<'a>, depth: usize, out: &mut Vec<ParseNode<'a>>) -> Result<(), ExpansionError<'a>> {
        match node {
            ParseNode::List { nodes, .. } => {
                let args = nodes.get(1..).unwrap_or_default();
                match called(node) {
                    Some(kind @ ("unquote" | "splice")) if depth == 0 => {
                        let mut expanded = self.expand_nodes(args)?.into_vec();
                        if kind == "splice" {
                            expanded = match <Box<[_; 1]>>::try_from(expanded.into_boxed_slice()) {
                                Ok(list) => match *list {
                                    [ParseNode::List { nodes, .. }] => nodes.items().collect(),
                                    [other] => return Err(error(format!(
                                        "`%splice` splices a list into its place, but got a {}.", other.node_type()), node)),
                                },
                                Err(nodes) if nodes.is_empty() => vec![],
                                Err(_) => return Err(error("`%splice` takes a single list.", node)),
                            };
                        }
                        if let Some(first) = expanded.first_mut() {
                            first.set_leading_whitespace(node.leading_whitespace().clone());
                        }
                        out.extend(expanded);
                    },
                    name => {
                        let depth = match name {
                            Some("quasi") => depth + 1,
                            Some("unquote" | "splice") => depth - 1,
                            _ => depth,
                        };
                        let mut items = Vec::with_capacity(nodes.len());
                        for item in nodes.items() {
                            self.quasi(&item, depth, &mut items)?;
                        }
                        out.push(list_node(node, items));
                    },
                }
            },
            ParseNode::Attribute { keyword, node: value, site, leading_whitespace } => {
                let mut values = vec![];
                self.quasi(value, depth, &mut values)?;
                let value = single(values.into_boxed_slice(), "An attribute's value", node)?;
                out.push(ParseNode::Attribute {
                    keyword: keyword.clone(),
                    node: Box::new(value),
                    site: *site,
                    leading_whitespace: leading_whitespace.clone(),
                });
            },
            atom => out.push(atom.clone()),
        }
        Ok(())
    }

    /// `(%type x)` gives what kind of node `x` is.
    pub(super) fn expand_type_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let value = self.expand_nodes(params)?;
        let kind = match &*value {
            [] => "nothing",
            [value] => match value {
                ParseNode::Symbol(_) => "symbol",
                ParseNode::Number(_) => "number",
                ParseNode::String(_) => "string",
                ParseNode::Raw(_) => "raw",
                ParseNode::List { .. } => "list",
                ParseNode::Attribute { .. } => "attribute",
            },
            _ => return Err(error("`%type` takes a single value.", node)),
        };
        Ok(Box::new([symbol_node(node, kind)]))
    }

    /// `(%list? x)`, `(%symbol? x)`, ..., whether `x` is that kind of node.
    pub(super) fn expand_type_predicate_macro(&self, kind: &str, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let value = self.expand_nodes(params)?;
        let [value] = &*value else {
            return Err(error(format!("`%{kind}?` takes a single value."), node));
        };
        let is = match kind {
            "symbol" => value.is_symbol(),
            "number" => value.is_number(),
            "string" => value.is_string(),
            "raw" => matches!(value, ParseNode::Raw(_)),
            "list" => value.is_list(),
            "attribute" => value.is_attribute(),
            _ => unreachable!("not a type predicate"),
        };
        Ok(Box::new([bool_node(node, is)]))
    }

    /// `(%attribute key value)` gives `:key value`.
    pub(super) fn expand_attribute_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [key, value] = &*params else {
            return Err(error("`%attribute` takes a key and a value: `(%attribute key value)`.", node));
        };
        let Some(key) = key.atomic() else {
            return Err(error(format!("An attribute's key must be text, but got a {}.", key.node_type()), node));
        };
        let mut value = value.clone();
        value.set_leading_whitespace(" ");
        Ok(Box::new([ParseNode::Attribute {
            keyword: key.value.clone(),
            node: Box::new(value),
            site: node.owned_site(),
            leading_whitespace: node.leading_whitespace().clone(),
        }]))
    }

    /// `(%dict ((a 1) (b 2)))` gives `(:a 1 :b 2)`, the reverse of `%items`.
    pub(super) fn expand_dict_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [pairs] = &*params else {
            return Err(error("`%dict` takes a list of `(key value)` pairs.", node));
        };
        let mut attributes = vec![];
        for pair in list_of(pairs, node, "`%dict`'s argument")? {
            let Some([key, value]) = pair.list().map(|nodes| &**nodes) else {
                return Err(error("Each item of `%dict`'s list must be a pair, `(key value)`.", &pair));
            };
            let Some(key) = key.atomic() else {
                return Err(error(format!("A key must be text, but got a {}.", key.node_type()), &pair));
            };
            let mut value = value.clone();
            value.set_leading_whitespace(" ");
            attributes.push(ParseNode::Attribute {
                keyword: key.value.clone(),
                node: Box::new(value),
                site: pair.owned_site(),
                leading_whitespace: "".into(),
            });
        }
        Ok(Box::new([list_node(node, spaced(attributes))]))
    }

    /// `(%read "(a b)")` parses text as seam code, without expanding it.
    pub(super) fn expand_read_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [text] = &*params else {
            return Err(error("`%read` takes the text to read.", node));
        };
        let Some(text) = text.atomic() else {
            return Err(error(format!("`%read` reads text, but got a {}.", text.node_type()), node));
        };
        let name = format!("{} (read)", node.site().source());
        let parser = self.register_parser(Parser::new(Lexer::new(name, text.value.to_string())));
        let mut tree = parser.parse().map_err(|err| error(format!("{err}"), node))?.into_vec();
        if let Some(first) = tree.first_mut() {
            first.set_leading_whitespace(node.leading_whitespace().clone());
        }
        Ok(tree.into_boxed_slice())
    }

    /// `(%map f (a b c))` gives the list of `f` applied to each item, with
    /// everything each call gives. Given the items directly, `(%map f a b c)`,
    /// it gives them without a list around them.
    pub(super) fn expand_map_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let Some((function, items)) = params.split_first() else {
            return Err(error("`%map` takes a macro and a list: `(%map f list)`.", node));
        };
        let mut mapped = vec![];
        for item in list_items(items) {
            mapped.extend(self.call(function, node, std::slice::from_ref(&item))?);
        }
        Ok(if let [ParseNode::List { .. }] = items {
            Box::new([list_node(node, without_leading(mapped))])
        } else {
            mapped.into_boxed_slice()
        })
    }

    /// `(%filter predicate (a b c))`, the items the predicate is true for.
    pub(super) fn expand_filter_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let Some((predicate, items)) = params.split_first() else {
            return Err(error("`%filter` takes a predicate and a list: `(%filter f list)`.", node));
        };
        let mut kept = vec![];
        for item in list_items(items) {
            if truthy(&self.call(predicate, node, std::slice::from_ref(&item))?) {
                kept.push(item);
            }
        }
        Ok(if let [ParseNode::List { .. }] = items {
            Box::new([list_node(node, without_leading(kept))])
        } else {
            kept.into_boxed_slice()
        })
    }

    /// `(%fold f initial (a b c))` gives `(%f (%f (%f initial a) b) c)`.
    pub(super) fn expand_fold_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [function, initial, list] = &*params else {
            return Err(error("`%fold` takes a macro, an initial value and a list: `(%fold f initial list)`.", node));
        };
        let mut accumulator = initial.clone();
        for item in list_of(list, node, "`%fold`'s last argument")? {
            accumulator = self.call_one(function, node, &[accumulator, item])?;
        }
        accumulator.set_leading_whitespace(node.leading_whitespace().clone());
        Ok(Box::new([accumulator]))
    }

    /// `(%find predicate list)`, the first item the predicate is true for (or nothing),
    /// `(%any predicate list)` and `(%all predicate list)`.
    pub(super) fn expand_find_macro(&self, name: &str, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [predicate, list] = &*params else {
            return Err(error(format!("`%{name}` takes a predicate and a list: `(%{name} f list)`."), node));
        };
        let ParseNode::List { nodes, .. } = list else {
            return Err(error(format!("`%{name}`'s last argument must be a list, but got a {}.", list.node_type()), node));
        };
        for item in nodes.items() {
            let true_for_item = truthy(&self.call(predicate, node, std::slice::from_ref(&item))?);
            match name {
                "find" if true_for_item => {
                    let mut item = item;
                    item.set_leading_whitespace(node.leading_whitespace().clone());
                    return Ok(Box::new([item]));
                },
                "any" if true_for_item => return Ok(Box::new([bool_node(node, true)])),
                "all" if !true_for_item => return Ok(Box::new([bool_node(node, false)])),
                _ => {},
            }
        }
        Ok(match name {
            "find" => Box::new([]),
            _ => Box::new([bool_node(node, name == "all")]),
        })
    }

    /// `(%zip (a b) (1 2))` gives `((a 1) (b 2))`, as long as the shortest list.
    pub(super) fn expand_zip_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let mut lists = vec![];
        for list in &params {
            let ParseNode::List { nodes, .. } = list else {
                return Err(error(format!("`%zip` takes lists, but got a {}.", list.node_type()), node));
            };
            lists.push(nodes.items());
        }
        let mut zipped = vec![];
        if !lists.is_empty() {
            'zipping: loop {
                let mut tuple = Vec::with_capacity(lists.len());
                for list in &mut lists {
                    let Some(item) = list.next() else { break 'zipping };
                    tuple.push(item);
                }
                zipped.push(list_node(node, spaced(tuple)));
            }
        }
        Ok(Box::new([list_node(node, spaced(zipped))]))
    }

    /// `(%enumerate (a b))` gives `((0 a) (1 b))`, counting `:from` 0 by default.
    pub(super) fn expand_enumerate_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let (list, from) = match &*params {
            [list] => (list, 0),
            [list, ParseNode::Attribute { keyword, node: from, .. }] if keyword == "from" => {
                let Some(from) = from.atomic().and_then(|from| from.value.parse::<i64>().ok()) else {
                    return Err(error("`:from` must be a whole number.", node));
                };
                (list, from)
            },
            _ => return Err(error("`%enumerate` takes a list, and optionally `:from n`.", node)),
        };
        let items = list_of(list, node, "`%enumerate`'s argument")?;
        let pairs = items.into_iter().zip(from..).map(|(mut item, index)| {
            item.set_leading_whitespace(" ");
            let mut index = number_node(node, index.to_string());
            index.set_leading_whitespace("");
            list_node(node, vec![index, item])
        }).collect();
        Ok(Box::new([list_node(node, spaced(pairs))]))
    }

    /// `(%flatten (a (b (c))))` gives `(a b c)`, or only `:depth n` levels deep.
    pub(super) fn expand_flatten_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let (list, depth) = match &*params {
            [list] => (list, usize::MAX),
            [list, ParseNode::Attribute { keyword, node: depth, .. }] if keyword == "depth" => {
                let Some(depth) = depth.atomic().and_then(|depth| depth.value.parse::<usize>().ok()) else {
                    return Err(error("`:depth` must be a whole number.", node));
                };
                (list, depth)
            },
            _ => return Err(error("`%flatten` takes a list, and optionally `:depth n`.", node)),
        };
        fn flatten<'a>(items: Vec<ParseNode<'a>>, depth: usize, out: &mut Vec<ParseNode<'a>>) {
            for item in items {
                match item {
                    ParseNode::List { nodes, .. } if depth > 0 => flatten(nodes.items().collect(), depth - 1, out),
                    item => out.push(item),
                }
            }
        }
        let mut flat = vec![];
        flatten(list_of(list, node, "`%flatten`'s argument")?, depth, &mut flat);
        Ok(Box::new([list_node(node, spaced(flat))]))
    }

    /// `(%group-by f list)` gives `(:key1 (items...) :key2 (items...))`,
    /// grouping the items by what `f` gives for them, in the order first seen.
    pub(super) fn expand_group_by_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [function, list] = &*params else {
            return Err(error("`%group-by` takes a macro and a list: `(%group-by f list)`.", node));
        };
        let mut groups: Vec<(std::borrow::Cow<'a, str>, Vec<ParseNode<'a>>)> = vec![];
        for item in list_of(list, node, "`%group-by`'s last argument")? {
            let key = self.call_one(function, node, std::slice::from_ref(&item))?;
            let Some(key) = key.atomic().map(|key| key.value.clone()) else {
                return Err(error(format!("`%group-by`'s macro must give text to group by, but gave a {}.",
                    key.node_type()), node));
            };
            match groups.iter_mut().find(|(existing, _)| *existing == key) {
                Some((_, items)) => items.push(item),
                None => groups.push((key, vec![item])),
            }
        }
        let attributes = groups.into_iter().map(|(key, items)| {
            let mut items = list_node(node, spaced(items));
            items.set_leading_whitespace(" ");
            ParseNode::Attribute {
                keyword: key,
                node: Box::new(items),
                site: node.owned_site(),
                leading_whitespace: "".into(),
            }
        }).collect();
        Ok(Box::new([list_node(node, spaced(attributes))]))
    }

    /// `(%walk f tree)` rebuilds a tree from the bottom up, replacing every
    /// node with what `f` gives for it (after its own items are replaced),
    /// except attributes, whose values are replaced instead.
    /// Giving nothing removes a node, and giving several splices them in.
    pub(super) fn expand_walk_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let Some((function, trees)) = params.split_first() else {
            return Err(error("`%walk` takes a macro and a tree: `(%walk f tree)`.", node));
        };
        let mut out = vec![];
        for tree in trees {
            self.walk(function, node, tree, &mut out)?;
        }
        Ok(out.into_boxed_slice())
    }

    fn walk(&self, function: &ParseNode<'a>, call: &ParseNode<'a>, tree: &ParseNode<'a>, out: &mut Vec<ParseNode<'a>>) -> Result<(), ExpansionError<'a>> {
        let rebuilt = match tree {
            ParseNode::List { nodes, .. } => {
                let mut items = Vec::with_capacity(nodes.len());
                for item in nodes.items() {
                    self.walk(function, call, &item, &mut items)?;
                }
                list_node(tree, without_leading(items))
            },
            // An attribute is not a value itself, so only its value is walked.
            ParseNode::Attribute { keyword, node: value, site, leading_whitespace } => {
                let mut values = vec![];
                self.walk(function, call, value, &mut values)?;
                out.push(ParseNode::Attribute {
                    keyword: keyword.clone(),
                    node: Box::new(single(values.into_boxed_slice(), "A walked attribute's value", tree)?),
                    site: *site,
                    leading_whitespace: leading_whitespace.clone(),
                });
                return Ok(());
            },
            atom => atom.clone(),
        };
        let mut replaced = self.call(function, call, std::slice::from_ref(&rebuilt))?.into_vec();
        // What replaces a node takes its place, and its whitespace.
        if let Some(first) = replaced.first_mut() {
            first.set_leading_whitespace(tree.leading_whitespace().clone());
        }
        out.extend(replaced);
        Ok(())
    }

    /// `(%select h2 tree)` gives the list of every `(h2 ...)` within a tree,
    /// in order, and `(%select (h2 h3) tree)` those starting with any of them.
    pub(super) fn expand_select_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let Some((selector, trees)) = params.split_first() else {
            return Err(error("`%select` takes what to select and a tree: `(%select h2 tree)`.", node));
        };
        let heads: Vec<String> = match selector {
            ParseNode::List { nodes, .. } => nodes.items().filter_map(|head| head.atomic().map(|head| head.value.to_string())).collect(),
            selector => match selector.atomic() {
                Some(head) => vec![head.value.to_string()],
                None => return Err(error("`%select` selects lists by their first item (or any of a list of them).", node)),
            },
        };
        fn select<'a>(tree: &ParseNode<'a>, heads: &[String], out: &mut Vec<ParseNode<'a>>) {
            match tree {
                ParseNode::List { nodes, .. } => {
                    if nodes.first().and_then(ParseNode::atomic).is_some_and(|head| heads.iter().any(|h| *h == head.value)) {
                        out.push(tree.clone());
                    }
                    for item in nodes.items() {
                        select(&item, heads, out);
                    }
                },
                ParseNode::Attribute { node, .. } => select(node, heads, out),
                _ => {},
            }
        }
        let mut selected = vec![];
        for tree in trees {
            select(tree, &heads, &mut selected);
        }
        Ok(Box::new([list_node(node, spaced(selected))]))
    }

    /// `(%gensym)`, or `(%gensym name)`, gives a new symbol, different from any other.
    pub(super) fn expand_gensym_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let prefix = match &*params {
            [] => "gensym".to_owned(),
            [ParseNode::Symbol(name) | ParseNode::String(name)] => name.value.to_string(),
            _ => return Err(error("`%gensym` takes at most a name to start the symbol with.", node)),
        };
        let id = self.context.lambdas.get();
        self.context.lambdas.set(id + 1);
        Ok(Box::new([symbol_node(node, format!("__{prefix}{id}"))]))
    }

    /// `(%defined name)` is `macro` or `value` for what `name` is defined
    /// as (by `%define`, `%lambda`, a parameter...), or else `false`.
    pub(super) fn expand_defined_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [ParseNode::Symbol(name) | ParseNode::String(name)] = &*params else {
            return Err(error("`%defined` takes the name to look up.", node));
        };
        let name = name.value.strip_prefix('%').unwrap_or(&name.value);
        let kind = self.lookup(name, |definition| match definition {
            Definition::Macro(_) => "macro",
            Definition::Value(_) | Definition::Thunk(..) => "value",
        });
        Ok(Box::new([symbol_node(node, kind.unwrap_or("false"))]))
    }

    /// `(%macroexpand (%f a b))` expands one call of a macro a single step:
    /// its body, with its parameters replaced by their arguments, but none of
    /// the macros within it expanded. A built-in macro is expanded fully.
    pub(super) fn expand_macroexpand_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let [call] = params else {
            return Err(error("`%macroexpand` takes one macro call, `(%macroexpand (%f ...))`.", node));
        };
        // The call may be written out, or come from a variable.
        let call = if called(call).is_some() {
            call.clone()
        } else {
            single(self.expand_node(call)?, "`%macroexpand`'s argument", node)?
        };
        let Some(name) = called(&call) else {
            return Err(error("`%macroexpand` takes a macro call, `(%f ...)`.", &call));
        };
        let arguments = &call.list().map_or(&[][..], |nodes| nodes)[1..];
        let Some(mac) = self.lookup(name, |definition| match definition {
            Definition::Macro(mac) => Some(*mac),
            _ => None,
        }).flatten() else {
            return self.expand_node(&call);
        };
        let arguments = self.macro_arguments(mac, arguments)?;
        let subcontext = self.child_of(mac.env);
        let substituted = (|| {
            subcontext.bind_list(&call, &mac.params, &arguments)?;
            subcontext.check_types(mac)?;
            let parameters = subcontext.scope.definitions.borrow();
            let mut out = vec![];
            for node in &mac.body {
                substitute(node, &|name| parameters.get(name).and_then(|definition| match definition {
                    Definition::Value(nodes) | Definition::Thunk(nodes, ..) => Some(nodes.clone()),
                    Definition::Macro(_) => None,
                }), &mut out);
            }
            Ok(out)
        })();
        subcontext.release();
        let mut substituted = substituted?;
        if let Some(first) = substituted.first_mut() {
            first.set_leading_whitespace(node.leading_whitespace().clone());
        }
        Ok(substituted.into_boxed_slice())
    }
}

/// Replace each `%name` symbol that `lookup` finds with its nodes.
fn substitute<'a>(node: &ParseNode<'a>, lookup: &dyn Fn(&str) -> Option<ParseTree<'a>>, out: &mut Vec<ParseNode<'a>>) {
    match node {
        ParseNode::Symbol(symbol) if let Some(mut nodes) = symbol.macro_name().and_then(lookup).map(<[_]>::into_vec) => {
            if let Some(first) = nodes.first_mut() {
                first.set_leading_whitespace(symbol.leading_whitespace.clone());
            }
            out.extend(nodes);
        },
        ParseNode::List { nodes, .. } => {
            let mut items = Vec::with_capacity(nodes.len());
            for item in nodes.items() {
                substitute(&item, lookup, &mut items);
            }
            out.push(list_node(node, items));
        },
        ParseNode::Attribute { keyword, node: value, site, leading_whitespace } => {
            let mut values = vec![];
            substitute(value, lookup, &mut values);
            let value = if values.len() == 1 { values.swap_remove(0) } else { (**value).clone() };
            out.push(ParseNode::Attribute {
                keyword: keyword.clone(),
                node: Box::new(value),
                site: *site,
                leading_whitespace: leading_whitespace.clone(),
            });
        },
        atom => out.push(atom.clone()),
    }
}
