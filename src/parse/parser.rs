use std::{fmt, error::Error};
use super::tokens::{self, Kind, Site, Token};

#[derive(Debug, Clone)]
pub struct Node {
    pub site : Site,
    pub value : String
}

impl Node {
    pub fn new(value : &str, site : &Site) -> Self {
        Self {
            site:   site.to_owned(),
            value: value.to_owned()
        }
    }
}

#[derive(Debug, Clone)]
pub struct AttributeNode {
    pub keyword : String,
    pub node : Box<ParseNode>,
    pub site : Site
}

#[derive(Debug, Clone)]
pub enum ParseNode {
    Symbol(Node),
    Number(Node),
    String(Node),
    List(Vec<ParseNode>),
    Attribute(AttributeNode)
}

impl ParseNode {
    pub fn symbolic(&self) -> Option<Node> {
        match self {
            Self::Symbol(node)
            | Self::Number(node) => Some(node.to_owned()),
            _ => None
        }
    }
    pub fn atomic(&self) -> Option<Node> {
        match self {
            Self::Symbol(node)
            | Self::Number(node)
            | Self::String(node) => Some(node.to_owned()),
            _ => None
        }
    }
    pub fn site(&self) -> Site {
        match self {
            Self::Symbol(node)
            | Self::Number(node)
            | Self::String(node) => node.site.to_owned(),
            Self::List(list) => {
                if let Some(head) = list.first() {
                    head.site()
                } else {
                    panic!("No empty lists should be allowed.")
                }
            },
            Self::Attribute(attr) => attr.site.to_owned(),
        }
    }
}

pub type ParseTree = Vec<ParseNode>;

pub trait SearchTree {
    /// Search the parse-tree for a specific node with a specific value.
    fn search_node(&self, kind : SearchType,
                   value : &str,
                   case_insensitive : bool,
                   level : usize) -> Option<ParseNode>;
}

#[derive(Clone, Copy, PartialEq)]
pub enum SearchType {
    ListHead, ListMember,
    Symbol, Number, String,
    Attribute
}

impl SearchTree for ParseTree {
    fn search_node(&self, kind : SearchType, value : &str,
                   insensitive : bool, level: usize) -> Option<ParseNode> {
        if level == 0 {
            return None;
        }

        let is_equal = |string: &str| if insensitive {
            string.to_lowercase() == value.to_lowercase()
        } else {
            string == value
        };

        for node in self {
            let found = match node {
                ParseNode::List(nodes) => {
                    if kind == SearchType::ListHead {
                        if let Some(Some(caller)) = nodes.get(0).map(ParseNode::atomic) {
                            if is_equal(&caller.value) {
                                return Some(node.clone());
                            }
                        }
                    }
                    nodes.search_node(kind, value, insensitive, level - 1)
                },
                ParseNode::Symbol(name) => {
                    if kind == SearchType::Symbol && is_equal(&name.value) {
                        Some(node.clone())
                    } else {
                        None
                    }
                },
                ParseNode::String(name) => {
                    if kind == SearchType::String && is_equal(&name.value) {
                        Some(node.clone())
                    } else {
                        None
                    }
                },
                ParseNode::Number(name) => {
                    if kind == SearchType::Number && is_equal(&name.value) {
                        Some(node.clone())
                    } else {
                        None
                    }
                },
                ParseNode::Attribute(attr) => {
                    if kind == SearchType::Attribute {
                        if is_equal(&attr.keyword) {
                            return Some(node.clone());
                        }
                    }
                    let singleton : ParseTree = vec![*attr.node.clone()];
                    singleton.search_node(kind, value, insensitive, level - 1)
                }
            };

            if found.is_some() {
                return found;
            }
        }

        None
    }
}

#[derive(Debug, Clone)]
pub struct ParseError(pub String, pub Site);

impl fmt::Display for ParseError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[**] Parse Error {}: {}",
            self.1, self.0)
    }
}

impl Error for ParseError { }

fn parse_atomic(token : &Token) -> Result<ParseNode, ParseError> {
    let node = Node::new(&token.value, &token.site);
    match token.kind {
        Kind::Symbol => Ok(ParseNode::Symbol(node)),
        Kind::String => Ok(ParseNode::String(node)),
        Kind::Number => Ok(ParseNode::Number(node)),
        Kind::Whitespace => Ok(ParseNode::String(node)),
        _ => Err(ParseError(
            String::from("Atomic token not found here."),
            token.site.clone()))
    }
}

pub fn parse(tokens : &[Token])
    -> Result<(ParseNode, &[Token]), ParseError> {
    let token = &tokens[0];
    match token.kind {
        Kind::LParen => {
            // Parse list.
            let open_paren = token.site.clone();
            let mut slice = &tokens[1..];
            if slice.is_empty() {
                return Err(ParseError(
                    "Expected `)' (closing parenthesis), got EOF."
                    .to_owned(), token.site.clone()));
            }
            // Ignore leading white space in head of list.
            if slice[0].kind == Kind::Whitespace {
                slice = &slice[1..];
            }
            let mut elements = Vec::new();
            let mut token = &slice[0];

            let mut i = 0;
            loop {
                i += 1;
                if slice.is_empty() {
                    return Err(ParseError(
                        "Expected `)' (closing parenthesis), got EOF."
                        .to_owned(), token.site.clone()));
                }
                token = &slice[0];
                if token.kind == Kind::RParen
                    { break; }  // End of list.
                if token.kind == Kind::Whitespace && i == 2 {
                    // Skip whitespace immediately after head.
                    slice = &slice[1..];
                    continue;
                }

                let (element, left) = parse(&slice)?;
                elements.push(element);
                slice = left;
            }
            slice = &slice[1..];  // Ignore last r-paren.
            if elements.is_empty() {
                // Empty lists have an invisible empty symbol in them.
                let node = Node::new("", &open_paren);
                elements.push(ParseNode::Symbol(node));
            }
            Ok((ParseNode::List(elements), slice))
        },
        Kind::Keyword => {
            // Parse second token, make attribute.
            let (node, mut slice) = parse(&tokens[1..])?;
            let attribute = AttributeNode {
                keyword: token.value[1..].to_owned(),
                node: Box::new(node),
                site: token.site.to_owned()
            };
            // White space after attributes don't count.
            if let Some(next) = slice.first() {
                if next.kind == Kind::Whitespace {
                    slice = &slice[1..];
                }
            }
            Ok((ParseNode::Attribute(attribute), slice))
        },
        Kind::RParen => {
            Err(ParseError("Unexpected `)' (closing parenthesis). \
                Perhaps you forgot an opening parenthesis?".to_owned(),
                token.site.clone()))
        },
        _ => {  // Any atomic tokens.
            Ok((parse_atomic(&token)?, &tokens[1..]))
        }
    }
}

pub fn parse_stream(tokens: tokens::TokenStream)
    -> Result<ParseTree, ParseError> {
    let mut tree = Vec::new();
    let mut slice = &tokens[..];
    while !slice.is_empty() {
        let (node, next) = parse(slice)?;
        tree.push(node);
        slice = next;
    }
    Ok(tree)
}

/// Strip any pure whitespace (and annotation) nodes from the tree.
pub fn strip(tree : &[ParseNode], strip_attributes : bool) -> ParseTree {
    let mut stripped = tree.to_owned();
    stripped.retain(|branch| {
        match branch {
            ParseNode::String(node)  => !node.value.trim().is_empty(),
            ParseNode::Attribute(_) => !strip_attributes,
            _ => true
        }
    });
    for branch in stripped.iter_mut() {
        if let ParseNode::List(ref mut list) = branch {
            *list = strip(list, strip_attributes);
        }
    }
    stripped
}

/// Pretty printing for parse nodes.
#[cfg(feature="debug")]
impl fmt::Display for ParseNode {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseNode::Symbol(node)
            | ParseNode::Number(node)  => write!(f, "{}", &node.value),
            ParseNode::String(node)    => {
                if node.value.trim().is_empty() {
                    write!(f, "")
                } else {
                    write!(f, "\"{}\"", &node.value)
                }
            },
            ParseNode::Attribute(attr) => write!(f, ":{} {}",
                &attr.keyword, &*attr.node),
            ParseNode::List(list) => if list.len() == 0 {
                write!(f, "()")
            } else if let [ single ] = list.as_slice() {
                write!(f, "({})", single)
            } else {
                write!(f, "({}{})", &list[0],
                list[1..].iter().fold(String::new(), |acc, elem| {
                    let nested = elem.to_string().split('\n')
                        .fold(String::new(), |acc, e|
                            acc + "\n  " + &e);
                    acc + &nested
                }))
            }
        }
    }
}

