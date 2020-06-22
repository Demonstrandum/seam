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
    pub node : Box<ParseNode>
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
}

pub type ParseTree = Vec<ParseNode>;

#[derive(Debug, Clone)]
pub struct ParseError(pub String, pub Site);

impl fmt::Display for ParseError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[**] Parse Error: `{}',\nAt: {:#?}",
            self.0, self.1)
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
            Ok((ParseNode::List(elements), slice))
        },
        Kind::Keyword => {
            // Parse second token, make attribute.
            let (node, mut slice) = parse(&tokens[1..])?;
            let attribute = AttributeNode {
                keyword: token.value[1..].to_owned(),
                node: Box::new(node)
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
            ParseNode::List(list) => write!(f, "({}{})", &list[0],
                list[1..].iter().fold(String::new(), |acc, elem| {
                    let nested = elem.to_string().split('\n')
                        .fold(String::new(), |acc, e|
                            acc + "\n  " + &e);
                    acc + &nested
                }))
        }
    }
}

