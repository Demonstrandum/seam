//! Expander macros argument parsing utilities.
use std::{collections::HashMap, iter::zip};
use std::fmt::Write as _;

use regex::Regex;

use super::{
    expander::ExpansionError,
    parser::{Node, ParseNode},
};

#[derive(Debug, Clone)]
pub enum ArgPredicate<'tree> {
    Exactly(String),
    Matching(Regex),
    Satisfying(fn(&ParseNode<'tree>) -> Result<(), ExpansionError<'tree>>),
}

impl<'tree> ArgPredicate<'tree> {
    pub fn check_node(&self, node: &Node<'tree>, parse_node: &ParseNode<'tree>) -> Result<(), ExpansionError<'tree>> {
        match self {
            Self::Exactly(value) => if node.value == *value { Ok(()) } else {
                Err(ExpansionError(
                    format!("value must be equal to `{value}'"),
                    node.site,
                ))
            },
            Self::Matching(expr) => if expr.is_match(&node.value) { Ok(()) } else {
                Err(ExpansionError(
                    format!("value must be match /{}/", expr.as_str()),
                    node.site,
                ))
            },
            Self::Satisfying(test) => test(parse_node),
        }
    }
    pub fn check(&self, node: &ParseNode<'tree>) -> Result<(), ExpansionError<'tree>> {
        match self {
            Self::Exactly(..) | Self::Matching(..) => if let Some(atomic) = node.atomic() {
                self.check_node(atomic, node)
            } else {
                // If used correctly, this should really be an unreachable!().
                Err(ExpansionError(
                    format!("Expected a literal, got a {} instead.", node.node_type()),
                    node.owned_site(),
                ))
            },
            Self::Satisfying(test) => test(node),
        }
    }
}

/// Type of argument, and what kind of
/// conditions they have to satisfy.
///     Number ⊆ Literal;
///     String ⊆ Literal;
///     Symbol ⊆ Symbolic;
///     Number ⊆ Symbolic;
///     Symbolic ⊆ Literal;
///     * ⊆ Any.
#[derive(Debug, Clone)]
pub enum ArgType<'tree> {
    Literal(Vec<ArgPredicate<'tree>>),
    String(Vec<ArgPredicate<'tree>>),
    Symbol(Vec<ArgPredicate<'tree>>),
    Number(Vec<ArgPredicate<'tree>>),
    Symbolic(Vec<ArgPredicate<'tree>>),
    List(Vec<ArgType<'tree>>),
    Any(Vec<ArgPredicate<'tree>>),
}

fn check_all<'tree>(preds: &Vec<ArgPredicate<'tree>>, node: &ParseNode<'tree>) -> Result<(), ExpansionError<'tree>> {
    if preds.is_empty() { return Ok(()); }
    let mut issues = vec![];
    for pred in preds {
        match pred.check(node) {
            Ok(()) => return Ok(()),
            Err(err) => issues.push(err),
        }
    }
    if issues.is_empty() { return Ok(()); }
    // Amalgamate errors.
    let mut error = String::new();
    if let Some(literal) = node.atomic() {
        let _ = writeln!(error, "This argument's value (`{}') did not satisfy one of the following:", literal.value);
    } else {
        let _ = writeln!(error, "This argument's value did not satisfy one of the following:");

    }
    for (i, issue) in issues.iter().enumerate() {
        let _ = write!(error, "    * {}", issue.0);
        if i != issues.len() - 1 {
            let _ = writeln!(error, "; or");
        }
    }
    let _ = write!(error, ".");
    Err(ExpansionError(error, node.owned_site()))
}

impl<'tree> ArgType<'tree> {
    #[must_use]
    pub fn name(&self) -> &'static str {
        use ArgType::{Literal, String, Symbol, Number, Symbolic, List, Any};
        match self {
            Literal(..) => "literal",
            String(..) => "string",
            Symbol(..) => "symbol",
            Number(..) => "number",
            Symbolic(..) => "symbolic",
            List(..) => "list",
            Any(..) => "any",
        }
    }

    pub fn check(&self, node: &ParseNode<'tree>) -> Result<(), ExpansionError<'tree>> {
        use ArgType::{Literal, Symbol, Symbolic, Any, String, Number, List};
        // Compute the generic type-mismatch error beforehand, even if not used.
        let mismatch = ExpansionError(
            format!("Expected a {} node, got a {} instead.", self.name(), node.node_type()),
            node.owned_site());
        match node {
            ParseNode::Symbol(..) => match self {
                Literal(pred) | Symbol(pred) | Symbolic(pred) | Any(pred) => check_all(pred, node),
                _ => Err(mismatch),
            },
            ParseNode::String(..) | ParseNode::Raw(..) => match self {
                Literal(pred) | String(pred) | Any(pred) => check_all(pred, node),
                _ => Err(mismatch),
            },
            ParseNode::Number(..) => match self {
                Literal(pred) | Symbolic(pred) | Number(pred) | Any(pred) => check_all(pred, node),
                _ => Err(mismatch),
            },
            ParseNode::List { nodes, .. } => match self {
                List(arg_types) => {
                    if !arg_types.is_empty() && nodes.len() != arg_types.len() {
                        return Err(ExpansionError(
                            format!("Unexpected number of items in list, expected {} items, got {}.",
                                arg_types.len(), nodes.len()),
                            node.owned_site()
                        ));
                    }
                    for (arg_type, node) in zip(arg_types, nodes) {
                        arg_type.check(node)?;
                    }
                    Ok(())
                },
                Any(preds) => check_all(preds, node),
                _ => Err(mismatch),
            },
            ParseNode::Attribute { keyword, .. } => match self {
                Any(pred) => check_all(pred, node),
                _ => Err(ExpansionError(format!("Unknown attribute `:{keyword}`."), node.owned_site()))
            },
        }
    }
}

/// Kind of argument (optional, mandatory).
#[derive(Debug, Clone)]
pub enum Arg<'tree> {
    Mandatory(ArgType<'tree>),
    Optional(ArgType<'tree>),
}

impl<'tree> Arg<'tree> {
    #[must_use]
    pub fn argtype(&self) -> &ArgType<'tree> {
        match self {
           Arg::Mandatory(typ) | Arg::Optional(typ) => typ
        }
    }
}

/// Positional or named argument position.
#[derive(Debug, Clone, Copy)]
pub enum ArgPos<'a> { Int(usize), Str(&'a str) }
impl From<usize> for ArgPos<'_> {
    fn from(value: usize) -> Self { ArgPos::Int(value) }
}
impl<'a> From<&'a str> for ArgPos<'a> {
    fn from(value: &'a str) -> Self { ArgPos::Str(value) }
}
impl<'a> From<ArgPos<'a>> for Option<usize> {
    fn from(value: ArgPos<'a>) -> Option<usize> {
        match value {
            ArgPos::Int(int) => Some(int),
            ArgPos::Str(_) => None,
        }
    }
}
impl<'a> From<ArgPos<'a>> for Option<&'a str> {
    fn from(value: ArgPos<'a>) -> Option<&'a str> {
        match value {
            ArgPos::Str(str) => Some(str),
            ArgPos::Int(_) => None,
        }
    }
}

/// Holds information as to what kind rules
/// must be satisfied for an argument's given
/// position.
/// Pattern pertains to how to argument sits
/// in the macro-call's argument list.
#[derive(Debug, Clone)]
struct ArgPattern<'tree> {
    argument: Arg<'tree>,
    pattern: fn(ArgPos<'_>) -> bool,
}

/// A complete description of how a macro's arguments
/// should be parsed.
#[derive(Debug, Clone)]
pub struct ArgRules<'tree> {
    patterns: Vec<ArgPattern<'tree>>,
    trailing: Option<ArgType<'tree>>,
}

impl<'tree> ArgRules<'tree> {
    #[must_use]
    pub fn new() -> Self {
        Self { patterns: Vec::new(), trailing: None }
    }
    /// Register a pattern to match.
    pub fn register(&mut self, matcher: fn(ArgPos<'_>) -> bool, arg: Arg<'tree>)
    {
        self.patterns.push(ArgPattern {
            argument: arg,
            pattern: matcher,
        });
    }
    /// Register matching on all remaining arguments.
    pub fn register_remaining(&mut self, arg_type: ArgType<'tree>) {
        self.trailing = Some(arg_type);
    }
    /// Turn this structure into a parser.
    pub fn parser<'params>(self, call_node: &'params ParseNode<'tree>, params: &'params [ParseNode<'tree>]) -> Result<ArgParser<'params, 'tree>, ExpansionError<'tree>> {
        ArgParser::new(self, call_node, params)
    }
    /// Count how many mandatory arguments there are.
    #[must_use]
    pub fn count_mandatory(&self) -> usize {
        let mut count = 0;
        for pattern in &self.patterns {
            if let Arg::Mandatory(..) = pattern.argument { count += 1 }
        }
        count
    }
}

impl Default for ArgRules<'_> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
pub struct ArgParser<'params, 'tree> {
    pub call_node: &'params ParseNode<'tree>,
    pub rules: ArgRules<'tree>,
    pub positional: HashMap<usize, &'params ParseNode<'tree>>,
    pub named: HashMap<&'params str, &'params ParseNode<'tree>>,
    pub trailing: Vec<&'params ParseNode<'tree>>
}

impl<'params, 'tree> ArgParser<'params, 'tree> {
    pub fn new(rules: ArgRules<'tree>,
               call_node: &'params ParseNode<'tree>,
               params: &'params [ParseNode<'tree>])
    -> Result<Self, ExpansionError<'tree>>  {
        let mut position = 0;
        let mut positional = HashMap::with_capacity(params.len());
        let mut named = HashMap::with_capacity(params.len());
        let mut trailing = vec![];
        let mut mandatory_count: usize = 0;

        for param in params {
            // Register each argument with the parser.
            let (matcher, param_node): (ArgPos<'params>, &'params ParseNode) =
                if let ParseNode::Attribute { keyword, node, .. } = param {
                    (ArgPos::Str(keyword), node)
                } else {
                    position += 1;
                    (ArgPos::Int(position), param)
                };
            // Check if they do actually match with any of the rules.
            let mut arg_rule = None;
            for rule in &rules.patterns {
                // First check that there is a valid place for this argument.
                let is_valid_argument = (rule.pattern)(matcher);
                if is_valid_argument {
                    arg_rule = Some(rule);
                    break;
                }
            }
            // If the position rule does not match any specified argument,
            // check if it can be given as trailing argument.
            match arg_rule {
                Some(rule) => {
                    // Now check that the types are satisfied.
                    let argtype = rule.argument.argtype();
                    argtype.check(param_node)?;
                    // If so, insert the parameter.
                    match matcher {
                        ArgPos::Int(i) => positional.insert(i, param_node),
                        ArgPos::Str(k) => named.insert(k, param_node),
                    };
                    // Register if a mandatory argument was consumed.
                    if let Arg::Mandatory(..) = rule.argument { mandatory_count += 1 }
                },
                None => match &rules.trailing {
                    Some(trailing_rule) => {
                        // Check that the trailing type is satisfied.
                        trailing_rule.check(param)?;
                        // If so, push the argument.
                        trailing.push(param);
                    },
                    None => {
                        // Error on fact that an erroneous positional or named argument
                        // has been given. Only error on additional erroneous named
                        // arguments if trailing argument capture is enabled.
                        return Err(ExpansionError(if let ParseNode::Attribute { keyword, .. } = param {
                            format!("Unexpected named argument `:{keyword}`.")
                        } else {
                            format!("Unexpected positional argument in position {position}.")
                        }, param.owned_site()));
                    }
                }
            }
        }
        // After checking all the arguments are *valid*, now check
        // that all mandatory arguments are given.
        let needed_count =  rules.count_mandatory();
        let last_site = params.last().map_or(call_node.owned_site(), super::parser::ParseNode::owned_site);
        if mandatory_count < needed_count {
            return Err(ExpansionError(
                format!("Missing {} non-optional argument(s) from macro call.", needed_count - mandatory_count),
                last_site
            ));
        }

        Ok(Self { call_node, rules, positional, named, trailing })
    }

    pub fn get_optional<'k>(&self, key: impl Into<ArgPos<'k>>) -> Option<&'params ParseNode<'tree>> {
        match key.into() {
            ArgPos::Int(i) => self.positional.get(&i).copied(),
            ArgPos::Str(k) => self.named.get(k).copied(),
        }
    }

    pub fn get<'k>(&self, key: impl Into<ArgPos<'k>>) -> Result<&'params ParseNode<'tree>, ExpansionError<'tree>> {
        match key.into() {
            ArgPos::Int(i) => match self.positional.get(&i) {
                Some(value) => Ok(*value),
                None => Err(ExpansionError(
                    format!("Argument in position {i} not given."),
                    self.call_node.owned_site(),
                )),
            },
            ArgPos::Str(k) => match self.named.get(k) {
                Some(value) => Ok(*value),
                None => Err(ExpansionError(
                    format!("Named argument :{k} not given."),
                    self.call_node.owned_site(),
                )),
            },
        }
    }
}

pub fn extract_literal(node: ParseNode<'_>) -> Result<Node<'_>, ExpansionError<'_>> {
    match node {
        ParseNode::Symbol(lit)
      | ParseNode::Number(lit)
      | ParseNode::String(lit)
      | ParseNode::Raw(lit) => Ok(lit),
        _ => Err(ExpansionError(
            format!("Expected a literal, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_string(node: ParseNode<'_>) -> Result<Node<'_>, ExpansionError<'_>> {
    match node {
        ParseNode::String(string)
      | ParseNode::Raw(string) => Ok(string),
        _ => Err(ExpansionError(
            format!("Expected a string, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_symbol(node: ParseNode<'_>) -> Result<Node<'_>, ExpansionError<'_>> {
    match node {
        ParseNode::Symbol(sym) => Ok(sym),
        _ => Err(ExpansionError(
            format!("Expected a symbol, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_number(node: ParseNode<'_>) -> Result<Node<'_>, ExpansionError<'_>> {
    match node {
        ParseNode::Number(lit) => Ok(lit),
        _ => Err(ExpansionError(
            format!("Expected a number, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_symbolic(node: ParseNode<'_>) -> Result<Node<'_>, ExpansionError<'_>> {
    match node {
        ParseNode::Symbol(sym)
      | ParseNode::Number(sym) => Ok(sym),
        _ => Err(ExpansionError(
            format!("Expected a symbolic literal, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_list(node: ParseNode<'_>) -> Result<Vec<ParseNode<'_>>, ExpansionError<'_>> {
    match node {
        ParseNode::List { nodes, .. } => Ok(nodes.to_vec()),
        _ => Err(ExpansionError(
            format!("Expected a list, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_any(node: ParseNode<'_>) -> Result<ParseNode<'_>, ExpansionError<'_>> {
    Ok(node)
}

// Same as above but does not move the node.

pub fn extract_literal_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<&'b Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Symbol(lit)
      | ParseNode::Number(lit)
      | ParseNode::String(lit)
      | ParseNode::Raw(lit) => Ok(lit),
        _ => Err(ExpansionError(
            format!("Expected a literal, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_string_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<&'b Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::String(string)
      | ParseNode::Raw(string) => Ok(string),
        _ => Err(ExpansionError(
            format!("Expected a string, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_symbol_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<&'b Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Symbol(sym) => Ok(sym),
        _ => Err(ExpansionError(
            format!("Expected a symbol, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_number_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<&'b Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Number(lit) => Ok(lit),
        _ => Err(ExpansionError(
            format!("Expected a number, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_symbolic_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<&'b Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Symbol(sym)
      | ParseNode::Number(sym) => Ok(sym),
        _ => Err(ExpansionError(
            format!("Expected a symbolic literal, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_list_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<Vec<&'b ParseNode<'a>>, ExpansionError<'a>> {
    match node {
        ParseNode::List { nodes, .. } => Ok(nodes.iter().collect()),
        _ => Err(ExpansionError(
            format!("Expected a list, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_any_ref<'a, 'b>(node: &'b ParseNode<'a>) -> Result<&'b ParseNode<'a>, ExpansionError<'a>> {
    Ok(node)
}
