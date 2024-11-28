//! Expander macros argument parsing utilities.
use std::{borrow::Borrow, collections::HashMap};

use regex::Regex;

use super::{
    expander::ExpansionError,
    parser::{Node, ParseNode, ParseTree},
};

pub enum ArgPredicate {
    Exactly(String),
    Matching(Regex),
    Satisfying(Box<dyn Fn(ParseNode) -> bool>),
}

/// Type of argument, and what kind of
/// conditions they have to satisfy.
///     Number ⊆ Literal;
///     String ⊆ Literal;
///     Symbol ⊆ Symbolic;
///     Number ⊆ Symbolic;
///     Symbolic ⊆ Literal;
///     * ⊆ Any.
pub enum ArgType {
    Literal(Vec<ArgPredicate>),
    String(Vec<ArgPredicate>),
    Symbol(Vec<ArgPredicate>),
    Number(Vec<ArgPredicate>),
    Symbolic(Vec<ArgPredicate>),
    List(Vec<ArgType>),
    Any(Vec<ArgType>),
}

/// Kind of arguemnt type (optional, mandatory).
pub enum Arg {
    Mandatory(ArgType),
    Optional(ArgType),
}

/// Positonal or named argument position.
enum ArgPos<'a> { Int(usize), Str(&'a str) }
/// What kind of types can be matched against
/// when determining an arguments positionality.
pub trait ArgMatcher {
    fn unwrap(&self) -> ArgPos;
}
impl ArgMatcher for usize {
    fn unwrap(&self) -> ArgPos { ArgPos::Int(*self) }
}
impl ArgMatcher for &str {
    fn unwrap(&self) -> ArgPos { ArgPos::Str(self) }
}
impl From<&Box<dyn ArgMatcher>> for Option<usize> {
    fn from(value: &Box<dyn ArgMatcher>) -> Option<usize> {
        match value.unwrap() {
            ArgPos::Int(int) => Some(int),
            _ => None,
        }
    }
}
impl<'a> From<&'a Box<dyn ArgMatcher + 'a>> for Option<&'a str> {
    fn from(value: &'a Box<dyn ArgMatcher + 'a>) -> Option<&'a str> {
        match value.unwrap() {
            ArgPos::Str(str) => Some(str),
            _ => None,
        }
    }
}
impl From<usize> for Box<dyn ArgMatcher> {
    fn from(value: usize) -> Box<dyn ArgMatcher> { Box::new(value) }
}
impl<'a> From<&'a str> for Box<dyn ArgMatcher + 'a> {
    fn from(value: &'a str) -> Box<dyn ArgMatcher + 'a> { Box::new(value) }
}
impl<'a> From<&'a String> for Box<dyn ArgMatcher + 'a> {
    fn from(value: &'a String) -> Box<dyn ArgMatcher + 'a> { Box::new(value.as_ref()) }
}

/// Holds information as to what kind rules
/// must be satsified for an argument's given
/// position.
/// Pattern pertains to how to argument sits
/// in the macro-call's argument list.
struct ArgPattern<'a> {
    argument: Arg,
    pattern: Box<dyn Fn(&Box<dyn ArgMatcher + 'a>) -> bool>,
}

/// A complete description of how a macro's arguments
/// should be parsed.
pub struct ArgRules<'a> {
    patterns: Vec<ArgPattern<'a>>,
    trailing: Option<ArgType>,
}

impl<'a> ArgRules<'a> {
    pub fn new() -> Self {
        Self { patterns: Vec::new(), trailing: None }
    }
    /// Register a pattern to match.
    pub fn register<F>(&mut self, matcher: F, arg: Arg)
        where F: 'static + Fn(&Box<dyn ArgMatcher + 'a>) -> bool
    {
        self.patterns.push(ArgPattern {
            argument: arg,
            pattern: Box::new(matcher),
        });
    }
    /// Register matching on all remaining arguments.
    pub fn register_remaining(&mut self, arg_type: ArgType) {
        self.trailing = Some(arg_type);
    }
    /// Turn this structure into a parser.
    pub fn parser<'params, 'tree>(self, params: &'params Box<[ParseNode<'tree>]>) -> ArgParser<'params, 'a, 'tree> {
        ArgParser::new(self, params)
    }
}

/// Turns a pattern into a argument matching predicate.
macro_rules! predicate {
    // A literals which represent a potential exact match of the string values.
    ($lit:literal) => { ArgPredicate::Exactly(String::from($lit)) };
    // A pattern which can match against the argument.
    ($pat:pat) => {{
        fn matcher(arg: ParseNode) -> bool {
            use super::parser::IntoValue;
            match arg.into_value() {
                Some($pat) => true,
                _ => false,
            }
        }
        ArgPredicate::Satisfying(Box::new(matcher))
    }};
}

macro_rules! arg_type {
    (literal)  => { ArgType::Literal };
    (string)   => { ArgType::String };
    (symbol)   => { ArgType::Symbol };
    (number)   => { ArgType::Number };
    (symbolic) => { ArgType::Symbolic };
    (list)     => { ArgType::List };
    (any)      => { ArgType::Any };
}

macro_rules! argument_type {
    ($typ:ident) => {{ ArgType::Literal(vec![]) }};
    ($typ:ident[ $($preds:literal),+ ]) => {{
        arg_type!($typ)(vec![ $( predicate!($preds) ),+ ])
    }};
    ($typ:ident ( $($preds:pat),+ )) => {{
        arg_type!($typ)(vec![ $( predicate!($preds) ),+ ])
    }};
    ($typ:ident fn($($var:tt)+) { $($body:tt)* }) => {{
        fn predicate($($var)+) -> bool { $($body)* }
        let arg_pred = ArgPredicate::Satisfying(Box::new(predicate));
        arg_type!($typ)(vec![arg_pred])
    }};
}

macro_rules! register_position_pattern {
    ($ctx:expr, $n:pat, $arg:expr) => {
        fn position_matcher(pattern: &Box<dyn ArgMatcher>) -> bool {
            match pattern.into() {
                Some($n) => true,
                _ => false,
            }
        }
        let ctx: &mut ArgRules = $ctx;
        let arg: Arg = $arg;
        ctx.register(position_matcher, arg);
    };
}

macro_rules! _argument {
    // The pattern for a mandatory argument.
    ($ctx:expr => mandatory($n:pat): $($kind:tt)+) => {
        {
            let arg_type = argument_type!($($kind)+);
            let arg = Arg::Mandatory(arg_type);
            let ctx: &mut ArgRules = $ctx;
            register_position_pattern!(ctx, $n, arg);
        }
    };
    // The pattern for an optional argument.
    ($ctx:expr => optional($n:pat): $($kind:tt)+) => {
        {
            let arg_type = argument_type!($($kind)+);
            let arg = Arg::Optional(arg_type);
            let ctx: &mut ArgRules = $ctx;
            register_position_pattern!(ctx, $n, arg);
        }
    };
    // The pattern for an any remaining argument.
    ($ctx:expr => rest: $($kind:tt)+) => {
        {
            let arg_type = argument_type!($($kind)+);
            let ctx: &mut ArgRules = $ctx;
            ctx.register_remaining(arg_type);
        }
    };
}

/// See <https://stackoverflow.com/a/74971086/13162100>.
#[macro_export]
macro_rules! arguments {
    ($ctx:expr => @accumulate [ $($accumulated:tt)* ] [ ]) => { [ $($accumulated)* ] };
    ($ctx:expr => @accumulate [ $($accumulated:tt)* ] [ $($final_line:tt)* ]) => {
        [ $($accumulated)* _argument!( $ctx => $($final_line)+ ) ]
    };
    ($ctx:expr => @accumulate [ $($accumulated:tt)* ] [ $($this_line:tt)* ] , $($rest:tt)* ) => {
        arguments! {
            $ctx => @accumulate
                [ $($accumulated)* _argument!( $ctx => $($this_line)* ), ]
                [ ] $($rest)*
        }
    };
    ($ctx:expr => @accumulate [ $($accumulated:tt)* ] [ $($this_line:tt)* ] $current:tt $($rest:tt)* ) => {
        arguments! {
            $ctx => @accumulate
                [ $($accumulated)* ]
                [ $($this_line)* $current ]
                $($rest)*
        }
    };
    ( $($t:tt)* ) => {{
        let mut ctx = ArgRules::new();
        arguments! { &mut ctx => @accumulate [ ] [ ] $($t)* };
        ctx
    }}
}


// --- Proc Macro
use seam_argparse_proc_macro::*;


// ---

pub struct ArgParser<'params: 'rules, 'rules, 'tree> {
    rules: ArgRules<'rules>,
    positional: HashMap<usize, &'params ParseNode<'tree>>,
    named: HashMap<String, &'params ParseNode<'tree>>,
}

impl<'params, 'rules, 'tree> ArgParser<'params, 'rules, 'tree> {
    pub fn new(rules: ArgRules<'rules>,
               params: &'params ParseTree<'tree>)
    -> Result<Self, ExpansionError<'tree>>  {
        let mut position = 0;
        let mut positional = HashMap::with_capacity(params.len());
        let mut named = HashMap::with_capacity(params.len());
        for param in params {
            let matcher: Box<dyn ArgMatcher>;
            // Register each argument with the parser.
            if let ParseNode::Attribute { keyword, node, .. } = param {
                named.insert(keyword.to_owned(), node.borrow());
                matcher = keyword.into();
            } else {
                positional.insert(position, param);
                position += 1;
                matcher = position.into();
            }
            // Check if they do actually match with any of the rules.
            let mut arg_rule = None;
            for rule in &rules.patterns {
                // First check that there is a valid place for this argument.
                let is_valid_argument = (rule.pattern)(&matcher);
                if !is_valid_argument {
                    arg_rule = Some(rule);
                    break;
                }
            }
            let Some(rule) = arg_rule else {
                // Error on fact that an errenous positional or named argument
                // has been given. Only error on additional errenous named
                // arguemnts if trailing argument capture is enabled.
                todo!()
            };
            // Now check that the types are satisfied.
            let arg = &rule.argument;
            // TODO: throw error when mismatched.
        }
        // After checking all the arguments are *valid*, now check
        // that all mandatory arguments are given.
        "todo";
        // Now check if trailing (variadic) arguments are permitted
        // (otherwise error on unexpected additional arguments).
        // And if so, that they all satisfy the trailing argument rule.
        "todo";

        Ok(Self { rules, positional, named, })
    }

    pub fn get<P>(&mut self, key: P) -> Result<ParseNode<'tree>, ExpansionError<'tree>>
        where P: Into<Box<dyn ArgMatcher>>
    {
        let matcher: &Box<dyn ArgMatcher> = &key.into();
        // Go through every pattern that could match against the argument
        // position given and check if they match.
        for argpat in &self.rules.patterns {
            let pat = &argpat.pattern;
            let did_match = pat(matcher);
            if did_match {
                match matcher.unwrap() {
                    ArgPos::Int(i) => {},
                    ArgPos::Str(k) => {},
                }
            }
        }

        todo!()
    }
}

pub enum _ArgType {
    Literal(Vec<ArgPredicate>),
    String(Vec<ArgPredicate>),
    Symbol(Vec<ArgPredicate>),
    Number(Vec<ArgPredicate>),
    Symbolic(Vec<ArgPredicate>),
    List(Vec<ArgType>),
    Any(Vec<ArgType>),
}

pub fn extract_literal<'a>(node: ParseNode<'a>) -> Result<Node<'a>, ExpansionError<'a>> {
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

pub fn extract_string<'a>(node: ParseNode<'a>) -> Result<Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::String(string)
      | ParseNode::Raw(string) => Ok(string),
        _ => Err(ExpansionError(
            format!("Expected a string, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_symbol<'a>(node: ParseNode<'a>) -> Result<Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Symbol(sym) => Ok(sym),
        _ => Err(ExpansionError(
            format!("Expected a symbol, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_number<'a>(node: ParseNode<'a>) -> Result<Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Number(lit) => Ok(lit),
        _ => Err(ExpansionError(
            format!("Expected a number, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_symbolic<'a>(node: ParseNode<'a>) -> Result<Node<'a>, ExpansionError<'a>> {
    match node {
        ParseNode::Symbol(sym)
      | ParseNode::Number(sym) => Ok(sym),
        _ => Err(ExpansionError(
            format!("Expected a symbolic literal, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_list<'a>(node: ParseNode<'a>) -> Result<Vec<ParseNode<'a>>, ExpansionError<'a>> {
    match node {
        ParseNode::List { nodes, .. } => Ok(nodes.to_vec()),
        _ => Err(ExpansionError(
            format!("Expected a list, got a {} instead.", node.node_type()),
            node.owned_site()
        ))
    }
}

pub fn extract_any<'a>(node: ParseNode<'a>) -> Result<ParseNode<'a>, ExpansionError<'a>> {
    Ok(node)
}
