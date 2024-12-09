use std::{error::Error, fmt, str::FromStr};
use unicode_width::UnicodeWidthStr;
use descape::UnescapeExt;

use super::{lexer::{LexError, Lexer}, tokens::{Kind, Site, Token}};

/// The [`Node`] type represents what atomic/literals are parsed
/// into; i.e. not compound types (e.g. lists, attributes).
/// These are just a common storage for the literals in [`ParseNode`].
#[derive(Debug, Clone)]
pub struct Node<'a> {
    pub value: String,
    pub site: Site<'a>,
    pub leading_whitespace: String,
}

impl<'a> PartialEq for Node<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<'a> Eq for Node<'a> { }

impl<'a> std::hash::Hash for Node<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl<'a> Node<'a> {
    pub fn new(value: &str, site: &Site<'a>, leading_whitespace: &str) -> Self {
        Self {
            site: site.to_owned(),
            value: value.to_owned(),
            leading_whitespace: leading_whitespace.to_owned(),
        }
    }
}

/// Parse nodes are the components of the syntax tree that
/// the source code is translated into.
/// These nodes are also produced at compile-time by the macro expander.
#[derive(Debug, Clone)]
pub enum ParseNode<'a> {
    Symbol(Node<'a>),
    Number(Node<'a>),
    String(Node<'a>),
    Raw(Node<'a>), //< Raw-content strings are not parsed, only expanded by macros.
    List {
        nodes: Box<[ParseNode<'a>]>,
        site: Site<'a>,
        end_token: Token<'a>,
        leading_whitespace: String,
    },
    Attribute {
        keyword: String,
        node: Box<ParseNode<'a>>,
        site: Site<'a>,
        leading_whitespace: String,
    },
}

impl<'a> PartialEq for ParseNode<'a> {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::Symbol(node0) => match other {
                Self::Symbol(node1) => node0 == node1,
                _ => false,
            },
            Self::Number(node0) => match other {
                Self::Number(node1) => node0 == node1,
                _ => false,
            },
            Self::String(node0) => match other {
                Self::String(node1) => node0 == node1,
                _ => false,
            },
            Self::Raw(node0) => match other {
                Self::Raw(node1) => node0 == node1,
                _ => false,
            },
            Self::List { nodes: nodes0, .. } => match other {
                Self::List { nodes: nodes1, .. } => nodes0 == nodes1,
                _ => false,
            },
            Self::Attribute { keyword: keyword0, node: node0, .. } => match other {
                Self::Attribute { keyword: keyword1, node: node1, .. } =>
                    keyword0 == keyword1 && node0 == node1,
                _ => false,
            }
        }
    }
}
impl<'a> Eq for ParseNode<'a> { }

impl<'a> std::hash::Hash for ParseNode<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Symbol(node) => {
                state.write_u8(0);
                node.hash(state);
            },
            Self::Number(node) => {
                state.write_u8(1);
                node.hash(state);
            },
            Self::String(node) =>{
                state.write_u8(2);
                node.hash(state);
            },
            Self::Raw(node) => {
                state.write_u8(3);
                node.hash(state);
            },
            Self::List { nodes, .. } => {
                state.write_u8(4);
                nodes.hash(state);
            },
            Self::Attribute { keyword, node, .. } => {
                state.write_u8(5);
                keyword.hash(state);
                node.hash(state);
            },
        }
    }
}

impl<'a> ParseNode<'a> {
    /// Returns true if and only if self is the empty list `()`.
    pub fn null(&self) -> bool {
        match self {
            Self::List { nodes, .. } => nodes.is_empty(),
            _ => false,
        }
    }

    /// Unwrap a literal node if it is a symbol or number.
    pub fn symbolic(&self) -> Option<&Node<'a>> {
        match self {
            Self::Symbol(ref node) | Self::Number(ref node) => Some(node),
            _ => None,
        }
    }

    /// Unwrap string-like nodes.
    pub fn string(&self) -> Option<&Node<'a>> {
        match self {
            Self::String(ref node) | Self::Raw(ref node) => Some(node),
            _ => None,
        }
    }

    /// Unwrap a number node into a [`Node<'a>`].
    pub fn number(&self) -> Option<&Node<'a>> {
        match self {
            Self::Number(ref node) => Some(node),
            _ => None,
        }
    }

    /// Unwrap a symbol node into a [`Node<'a>`].
    pub fn symbol(&self) -> Option<&Node<'a>> {
        match self {
            Self::Symbol(ref node) => Some(node),
            _ => None,
        }
    }

    /// Unwrap literal (atomic) nodes into their underlying [`Node`].
    pub fn atomic(&self) -> Option<&Node<'a>> {
        match self {
            Self::Symbol(ref node)
            | Self::Number(ref node)
            | Self::String(ref node)
            | Self::Raw(ref node) => Some(node),
            _ => None,
        }
    }

    /// Unwrap list node into vector of nodes.
    pub fn list(&self) -> Option<&ParseTree<'a>> {
        match self {
            Self::List { nodes, .. } => Some(nodes),
            _ => None,
        }
    }

    /// Unwrap attribute node into keyword and value.
    pub fn attribute(&self) -> Option<(&str, &Box<ParseNode<'a>>)> {
        match self {
            Self::Attribute { keyword, node, .. } => Some((keyword, node)),
            _ => None,
        }
    }

    /// Same as [`Self::atomic`], but consumes the node,
    /// returning an owned [`Node`].
    pub fn into_atomic(self) -> Option<Node<'a>> {
        match self {
            Self::Symbol(node)
            | Self::Number(node)
            | Self::String(node)
            | Self::Raw(node) => Some(node),
            _ => None,
        }
    }

    /// Get a reference to the parse node's underlying [`Site`].
    pub fn site(&self) -> &Site<'a> {
        match self {
            Self::Symbol(ref node)
            | Self::Number(ref node)
            | Self::String(ref node)
            | Self::Raw(ref node) => &node.site,
            Self::List { ref site, .. } => site,
            Self::Attribute { ref site, .. } => site,
        }
    }

    /// Clone the underlying [`Site`] of this parse node.
    pub fn owned_site(&self) -> Site<'a> {
        match self {
            Self::Symbol(node)
            | Self::Number(node)
            | Self::String(node)
            | Self::Raw(node) => node.site,
            Self::List { site, .. } => *site,
            Self::Attribute { site, .. } => *site,
        }
    }

    /// Get a reference to the underlying leading whitespace string
    /// of this parse node.
    pub fn leading_whitespace(&self) -> &str {
        match self {
            Self::Symbol(ref node)
            | Self::Number(ref node)
            | Self::String(ref node)
            | Self::Raw(ref node) => &node.leading_whitespace,
            Self::List { ref leading_whitespace, .. } => leading_whitespace,
            Self::Attribute { ref leading_whitespace, .. } => leading_whitespace,
        }
    }

    /// Modify the underlying leading whitespace stored for this parse node.
    pub fn set_leading_whitespace(&mut self, whitespace: String) {
        match self {
            Self::Symbol(ref mut node)
            | Self::Number(ref mut node)
            | Self::String(ref mut node)
            | Self::Raw(ref mut node) => node.leading_whitespace = whitespace,
            Self::List { ref mut leading_whitespace, .. } => *leading_whitespace = whitespace,
            Self::Attribute { ref mut leading_whitespace, .. } => *leading_whitespace = whitespace,
        };
    }

    /// Get a `&'static str` string name of what type of parse node this is.
    pub fn node_type(&self) -> &'static str {
        match self {
            Self::Symbol(..) => "symbol",
            Self::Number(..) => "number",
            Self::String(..) => "string",
            Self::Raw(..) => "raw-content string",
            Self::List { .. } => "list",
            Self::Attribute { .. } => "attribute",
        }
    }

    pub fn is_symbolic(&self) -> bool { self.symbolic().is_some() }
    pub fn is_atomic(&self) -> bool { self.atomic().is_some() }
    pub fn is_symbol(&self) -> bool { self.symbol().is_some() }
    pub fn is_number(&self) -> bool { self.number().is_some() }
    pub fn is_string(&self) -> bool { self.string().is_some() }
    pub fn is_list(&self) -> bool { self.list().is_some() }
    pub fn is_attribute(&self) -> bool { self.attribute().is_some() }
}

// Try to convert a [`ParseNode`] enum value into
// its underlying type (e.g. [`Node`], `Box<[Node]>`, etc.).

impl<'a> TryFrom<ParseNode<'a>> for Node<'a> {
    type Error = ();

    fn try_from(value: ParseNode<'a>) -> Result<Self, Self::Error> {
        match value.into_atomic() {
            Some(node) => Ok(node),
            None => Err(()),
        }
    }
}

impl<'a> TryFrom<ParseNode<'a>> for Box<[ParseNode<'a>]> {
    type Error = ();

    fn try_from(value: ParseNode<'a>) -> Result<Self, Self::Error> {
        match value {
            ParseNode::List { nodes, .. } => Ok(nodes),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<ParseNode<'a>> for Vec<ParseNode<'a>> {
    type Error = ();

    fn try_from(value: ParseNode<'a>) -> Result<Self, Self::Error> {
        let into: Result<Box<[ParseNode<'a>]>, Self::Error> = value.try_into();
        into.map(|b| b.to_vec())
    }
}

/// Trait determining if a [`ParseNode`] can be converted into
/// a value of a given (usually inferred) type.
pub trait IntoValue<'a, T>: Sized {
    fn into_value(&'a self) -> Option<T> { None }
}

/// A number type.
trait Num<Rhs = Self, Output = Self>:
    std::ops::Add<Rhs, Output = Output>
  + std::ops::Sub<Rhs, Output = Output>
  + std::ops::Mul<Rhs, Output = Output>
  + std::ops::Div<Rhs, Output = Output>
  + std::ops::Rem<Rhs, Output = Output> { }
impl Num for usize { }
impl Num for isize { }
impl Num for u32 { }
impl Num for i32 { }
impl Num for u64 { }
impl Num for i64 { }
impl Num for f32 { }
impl Num for f64 { }

/// Convert parse-node into value if said value is a number type.
impl<'a, T: Num + FromStr> IntoValue<'a, T> for ParseNode<'a> {
    fn into_value(&self) -> Option<T> {
        match self {
            ParseNode::Number(node) => node.value.parse().ok(),
            _ => None,
        }
    }
}

/// Convert parse-node into value if said value is a symbol/string type.
impl<'a> IntoValue<'a, &'a str> for ParseNode<'a> {
    fn into_value(&'a self) -> Option<&'a str> {
        match self {
            ParseNode::Symbol(node)
          | ParseNode::String(node)
          | ParseNode::Raw(node) => Some(node.value.as_ref()),
            _ => None,
        }
    }
}

/// TODO: Convert parse-node into value if said value is a list type.
/*
impl<'a, V> IntoValue<'a, &'a [V]> for ParseNode<'a> {
    fn into_value(&'a self) -> Option<&'a [V]> {
        match self {
            ParseNode::List { nodes, .. } => {
                let mut values = Vec::with_capacity(nodes.len());
                for node in nodes {
                    let Some(value) = node.into_value() else {
                        return None;
                    };
                    let value: V = value;
                    values.push(value)
                }
                // TODO: fix this.
                let values: &[V] = &*Box::leak(values.into_boxed_slice());
                Some(values)
            },
            _ => None,
        }
    }
}
*/

/// An array of parse nodes, like in a [`ParseNode::List`], never grows.
/// Hence we prefer the `Box<[...]>` representation over a `Vec<...>`.
pub type ParseTree<'a> = Box<[ParseNode<'a>]>;

#[derive(Debug, Clone)]
pub struct ParseError<'a>(pub String, pub Site<'a>);

impl<'a> fmt::Display for ParseError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ParseError(msg, site) = self;
        let line_prefix = format!("  {} |", site.line);
        let line_view = site.line_slice();
        writeln!(f, "{} {}", line_prefix, line_view)?;
        writeln!(f, "{:>prefix_offset$} {:~>text_offset$}{:^>length$}", "|", "", "",
            prefix_offset=UnicodeWidthStr::width(line_prefix.as_str()),
            text_offset=site.line_column() - 1,
            length=site.width())?;
        write!(f, "[**] Parse Error ({}:{}:{}): {}",
            site.source, site.line, site.line_column(), msg)
    }
}

impl<'a> Error for ParseError<'a> { }

/// Parser structure walks through source using lexer.
#[derive(Debug, Clone)]
pub struct Parser {
    lexer: Lexer, //< Parser owns a lexer.
}

impl<'a> Parser {
    pub fn new(lexer: Lexer) -> Self {
        Self { lexer }
    }

    pub fn get_source(&self) -> &str {
        self.lexer.get_source()
    }

    /// Parse whole source code, finishing off the lexer.
    pub fn parse(&'a self) -> Result<ParseTree<'a>, Box<dyn Error + 'a>> {
        let mut root: Vec<ParseNode> = Vec::new();
        while !self.lexer.eof() {
            let expr = self.parse_expr()?;
            root.push(expr);
        }
        return Ok(root.into_boxed_slice());
    }

    /// Produce a parse node from the current position in the lexer.
    pub fn parse_expr(&'a self) -> Result<ParseNode<'a>, Box<dyn Error + 'a>> {
        let token = self.lexer.peek()?;
        match token.kind {
            Kind::LParen => self.parse_list(),
            Kind::RParen => Err(ParseError(
                "Unexpected `)' closing parenthesis.".to_owned(),
                token.site.to_owned()))?,
            Kind::Keyword => self.parse_keyword(),
            Kind::Symbol => Ok(ParseNode::Symbol(self.parse_atomic()?)),
            // TODO: Parse (escpae) string-literals.
            Kind::String => Ok(ParseNode::String(self.parse_atomic()?)),
            Kind::Number => Ok(ParseNode::Number(self.parse_atomic()?)),
        }
    }

    /// Parse keyword-attribute pair.
    fn parse_keyword(&'a self) -> Result<ParseNode<'a>, Box<dyn Error + 'a>> {
        // Consume :keyword token.
        let token = self.lexer.consume()?;
        assert_eq!(token.kind, Kind::Keyword);
        // Check we are able to consume next expression for keyword's value.
        {
            let no_expr_error = ParseError(
                format!("Keyword `:{}' expects an expression following it.", token.value),
                token.site.to_owned());
            if self.lexer.eof() { Err(no_expr_error.clone())? ;}
            match self.lexer.peek()? {
                Token { kind: Kind::RParen, .. } => Err(no_expr_error)?,
                _ => ()
            }
        }
        // Otherwise, parse the value and combine the node.
        let value = self.parse_expr()?;
        Ok(ParseNode::Attribute {
            keyword: token.value.to_owned(),
            node: Box::new(value),
            site: token.site.to_owned(),
            leading_whitespace: token.leading_whitespace.to_owned(),
        })
    }

    /// Parse a literal node.
    /// This is where escapes in symbols and strings are handled.
    fn parse_atomic(&'a self) -> Result<Node<'a>, LexError<'a>> {
        let token = self.lexer.consume()?;
        let value = match token.kind {
            Kind::Symbol | Kind::Number | Kind::Keyword => escape_sanitize(token.value),
            Kind::String => escape_string(token.value, &token.site)?,
            _ => unreachable!("called `parse_atomic` on non-atomic token."),
        };
        Ok(Node {
            value,
            site: token.site.clone(),
            leading_whitespace: token.leading_whitespace.to_string(),
        })
    }

    /// Parse a list `( [...] )'.
    fn parse_list(&'a self) -> Result<ParseNode<'a>, Box<dyn Error + 'a>> {
        // Consumed the `(' token.
        let lparen = self.lexer.consume()?;
        assert_eq!(lparen.kind, Kind::LParen);
        // Collect list elements.
        let mut elements = Vec::new();
        let mut rparen: Option<Token> = None;
        while !self.lexer.eof() {
            // Keep parsing expressions until `)' is reached.
            let token = self.lexer.peek()?;
            if token.kind == Kind::RParen {
                rparen = Some(self.lexer.consume()?); // Swallow up `)'.
                break;
            }
            let expr = self.parse_expr()?;
            elements.push(expr);
        }
        // Closing parenthesis was never found.
        let Some(rparen) = rparen else {
            return Err(ParseError(
                "Expected `)' closing parenthesis.".to_owned(),
                lparen.site.to_owned()))?;
        };
        Ok(ParseNode::List {
            nodes: elements.into_boxed_slice(),
            site: lparen.site.to_owned(),
            end_token: rparen.to_owned(),
            leading_whitespace: lparen.leading_whitespace.to_owned(),
        })
    }
}

/// Sanitize any escaped characters by removing their leading backslash.
fn escape_sanitize(string: &str) -> String {
    let mut builder = String::with_capacity(string.len());
    let mut chars = string.chars();
    while let Some(c) = chars.next() {
        if c == '\\' { continue; }
        builder.push(c)
    }
    builder
}

/// Parse a string with its escapes.
/// **Note:** Uses the `descape` crate for now.
fn escape_string<'a>(string: &'a str, site: &Site<'a>) -> Result<String, LexError<'a>> {
    string.to_unescaped()
        .map(|s| s.to_string())
        .map_err(|invalid| {
            LexError(
                format!("Invalid escape `\\{}' at byte-index {}.",
                    string.chars().nth(invalid.index).unwrap_or('?'), invalid.index),
                site.clone())
        })
}

pub trait SearchTree<'a> {
    /// Search the parse-tree for a specific node with a specific value.
    fn search_node(&'a self, kind: SearchType,
                   value: &str,
                   case_insensitive: bool,
                   level: usize) -> Option<&'a ParseNode<'a>>;
}

#[derive(Clone, Copy, PartialEq)]
pub enum SearchType {
    ListHead, ListMember,
    Symbol, Number, String,
    Attribute,
    Any,
}

impl SearchType {
    pub fn is_a(self, kind: SearchType) -> bool {
        self == SearchType::Any || self == kind
    }
}

impl<'a> SearchTree<'a> for ParseNode<'a> {
    fn search_node(&'a self, kind: SearchType, value: &str,
                   insensitive: bool, level: usize) -> Option<&'a ParseNode<'a>> {
        if level == 0 {
            return None;
        }

        let is_equal = |string: &str| if insensitive {
            string.to_lowercase() == value.to_lowercase()
        } else {
            string == value
        };

        match self {
            ParseNode::List { nodes, .. } => {
                if kind.is_a(SearchType::ListHead) {
                    if let Some(Some(caller)) = nodes.get(0).map(ParseNode::atomic) {
                        if is_equal(&caller.value) {
                            return Some(self);
                        }
                    }
                }
                nodes.search_node(kind, value, insensitive, level - 1)
            },
            ParseNode::Symbol(name) => {
                if kind.is_a(SearchType::Symbol) && is_equal(&name.value) {
                    Some(self)
                } else {
                    None
                }
            },
            ParseNode::String(name) | ParseNode::Raw(name) => {
                if kind.is_a(SearchType::String) && is_equal(&name.value) {
                    Some(self)
                } else {
                    None
                }
            },
            ParseNode::Number(name) => {
                if kind.is_a(SearchType::Number) && is_equal(&name.value) {
                    Some(self)
                } else {
                    None
                }
            },
            ParseNode::Attribute { node, ref keyword, .. } => {
                if kind.is_a(SearchType::Attribute) {
                    if is_equal(keyword) {
                        return Some(node);
                    }
                }
                node.search_node(kind, value, insensitive, level - 1)
            },
        }
    }
}

impl<'a> SearchTree<'a> for ParseTree<'a> {
    fn search_node(&'a self, kind: SearchType, value: &str,
                   insensitive: bool, level: usize) -> Option<&'a ParseNode<'a>> {
        if level == 0 {
            return None;
        }

        for node in self {
            let found = node.search_node(kind, value, insensitive, level);
            if found.is_some() {
                return found;
            }
        }

        None
    }
}

/// Pretty printing for parse nodes.
impl<'a> fmt::Display for ParseNode<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseNode::Symbol(node)
            | ParseNode::Number(node) => write!(f, "{}{}", node.leading_whitespace, node.value),
            ParseNode::String(node)
            | ParseNode::Raw(node) => write!(f, "{}{:?}", node.leading_whitespace, node.value),
            ParseNode::Attribute { keyword, node, leading_whitespace, .. } =>
                write!(f, "{}:{}{}", leading_whitespace, keyword, &*node),
            ParseNode::List { nodes, leading_whitespace, end_token, .. } => {
                write!(f, "{}(", leading_whitespace)?;
                for node in nodes {
                    write!(f, "{}", node)?;
                }
                write!(f, "{})", end_token.leading_whitespace)
            }
        }
    }
}
