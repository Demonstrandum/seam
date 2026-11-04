//! Output JavaScript, written as s-expressions.
//! A list is a call, `(f a b)` → `f(a, b)`, unless it starts with an operator
//! or a keyword, e.g. `(+ a b)` → `a + b`, `(. a b)` → `a.b`,
//! `(const x 1)` → `const x = 1`, `(=> (x) (* x x))` → `(x) => x * x`.
//! A list of `:key value` attributes is an object, as with JSON.
//! Symbols and numbers are written as they are, and strings as JavaScript strings.

use super::{MarkupFormatter, GenerationError, Formatter};
use super::json::write_string;
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct JSFormatter<'a> {
    pub tree: ParseTree<'a>,
}

/// Operators written between their operands, `(+ a b c)` → `a + b + c`.
const BINARY: &[&str] = &[
    "+", "-", "*", "/", "%", "**",
    "==", "===", "!=", "!==", "<", ">", "<=", ">=",
    "&&", "||", "??", "&", "|", "^", "<<", ">>", ">>>",
    "in", "instanceof",
    "=", "+=", "-=", "*=", "/=", "%=", "**=", "&&=", "||=", "??=",
    "&=", "|=", "^=", "<<=", ">>=", ">>>=",
];
/// Operators written before their one operand, `(! a)` → `!a`
/// (`+` and `-` are too, when given one operand).
const UNARY: &[&str] = &["!", "~", "typeof", "void", "delete", "await"];
/// Keywords that make statements, which are not expressions.
const STATEMENTS: &[&str] = &[
    "const", "let", "var", "if", "for", "while", "return", "throw", "import", "export", "break", "continue",
];

type Result<'a> = std::result::Result<(), GenerationError<'a>>;

fn error<'a>(message: &str, node: &ParseNode<'a>) -> GenerationError<'a> {
    GenerationError::new("JavaScript", message, node.site())
}

/// The keyword or operator a list starts with (`+` and `-` are read as numbers).
fn head<'n>(node: &'n ParseNode) -> Option<&'n str> {
    match node {
        ParseNode::List { nodes, .. } => match nodes.first() {
            Some(ParseNode::Symbol(symbol)) => Some(&symbol.value),
            Some(ParseNode::Number(number)) if number.value.parse::<f64>().is_err() => Some(&number.value),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a node is a statement, and not an expression.
fn is_statement(node: &ParseNode) -> bool {
    head(node).is_some_and(|head| STATEMENTS.contains(&head))
        || (head(node) == Some("function") && matches!(node.list().map(|nodes| nodes.get(1)), Some(Some(ParseNode::Symbol(_)))))
}

/// Whether a key can be written without quotes, `{a: 1}` and `x.a`.
fn is_identifier(key: &str) -> bool {
    let mut chars = key.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_' || c == '$')
        && chars.all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

impl<'a> JSFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    /// Start a new line at an indentation level, when pretty-printing,
    /// or else separate with a space.
    fn newline(f: Formatter, indent: Option<usize>) -> Result<'a> {
        match indent {
            Some(indent) => write!(f, "\n{:width$}", "", width = 2 * indent)?,
            None => write!(f, " ")?,
        }
        Ok(())
    }

    /// Generate statements, one after another.
    fn generate_statements(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
        for (index, node) in nodes.iter().enumerate() {
            if index > 0 {
                Self::newline(f, indent)?;
            }
            Self::generate_statement(f, node, indent)?;
        }
        Ok(())
    }

    /// Generate a block of statements in braces. With `returns`, the last
    /// expression is returned, as it is the result of a function.
    fn generate_block(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>, returns: bool) -> Result<'a> {
        write!(f, "{{")?;
        let inner = indent.map(|indent| indent + 1);
        for (index, node) in nodes.iter().enumerate() {
            Self::newline(f, inner)?;
            if returns && index + 1 == nodes.len() && !is_statement(node) {
                write!(f, "return ")?;
                Self::generate_expression(f, node, inner, false)?;
                write!(f, ";")?;
            } else {
                Self::generate_statement(f, node, inner)?;
            }
        }
        if !nodes.is_empty() {
            Self::newline(f, indent)?;
        }
        write!(f, "}}")?;
        Ok(())
    }

    fn generate_statement(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
        let (Some(keyword), Some(nodes)) = (head(node), node.list()) else {
            Self::generate_expression(f, node, indent, false)?;
            write!(f, ";")?;
            return Ok(());
        };
        let args = &nodes[1..];
        match (keyword, args) {
            ("const" | "let" | "var", [name, rest @ ..]) => {
                write!(f, "{keyword} ")?;
                Self::generate_expression(f, name, indent, false)?;
                match rest {
                    [] => {},
                    [value] => {
                        write!(f, " = ")?;
                        Self::generate_expression(f, value, indent, false)?;
                    },
                    _ => return Err(error(&format!("`({keyword} name value)' takes one value."), node)),
                }
                write!(f, ";")?;
            },
            ("if", [condition, then, otherwise @ ..]) => {
                write!(f, "if (")?;
                Self::generate_expression(f, condition, indent, false)?;
                write!(f, ") ")?;
                Self::generate_branch(f, then, indent)?;
                match otherwise {
                    [] => {},
                    [otherwise] => {
                        write!(f, " else ")?;
                        if head(otherwise) == Some("if") {
                            Self::generate_statement(f, otherwise, indent)?;
                        } else {
                            Self::generate_branch(f, otherwise, indent)?;
                        }
                    },
                    _ => return Err(error("`(if condition then else)' takes at most one else branch, \
                                           use `(do ...)' for more statements.", node)),
                }
            },
            ("for", [name, ParseNode::Symbol(word), iterable, body @ ..]) if word.value == "of" || word.value == "in" => {
                write!(f, "for (const ")?;
                Self::generate_expression(f, name, indent, false)?;
                write!(f, " {} ", word.value)?;
                Self::generate_expression(f, iterable, indent, false)?;
                write!(f, ") ")?;
                Self::generate_block(f, body, indent, false)?;
            },
            ("while", [condition, body @ ..]) => {
                write!(f, "while (")?;
                Self::generate_expression(f, condition, indent, false)?;
                write!(f, ") ")?;
                Self::generate_block(f, body, indent, false)?;
            },
            ("return" | "throw", [value]) => {
                write!(f, "{keyword} ")?;
                Self::generate_expression(f, value, indent, false)?;
                write!(f, ";")?;
            },
            ("return" | "break" | "continue", []) => write!(f, "{keyword};")?,
            ("export", [ParseNode::Symbol(default), value]) if default.value == "default" => {
                write!(f, "export default ")?;
                Self::generate_expression(f, value, indent, false)?;
                write!(f, ";")?;
            },
            ("export", [statement]) if is_statement(statement) => {
                write!(f, "export ")?;
                Self::generate_statement(f, statement, indent)?;
            },
            // `(import { a, b } from "x")` is written word for word.
            ("import", [_, ..]) => {
                write!(f, "import")?;
                for word in args {
                    write!(f, " ")?;
                    Self::generate_expression(f, word, indent, false)?;
                }
                write!(f, ";")?;
            },
            ("function", [ParseNode::Symbol(_), ..]) => Self::generate_function(f, node, args, indent)?,
            _ if is_statement(node) => return Err(error(&format!("Malformed `{keyword}' statement."), node)),
            _ => {
                Self::generate_expression(f, node, indent, false)?;
                write!(f, ";")?;
            },
        }
        Ok(())
    }

    /// A branch of an `if`: a block, from `(do ...)` or a single statement.
    fn generate_branch(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
        match (head(node), node.list()) {
            (Some("do"), Some(nodes)) => Self::generate_block(f, &nodes[1..], indent, false),
            _ => Self::generate_block(f, std::slice::from_ref(node), indent, false),
        }
    }

    /// `(function name? (params...) body...)`, returning its last expression.
    fn generate_function(f: Formatter, node: &ParseNode<'a>, args: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
        let (name, rest) = match args {
            [ParseNode::Symbol(name), rest @ ..] => (Some(name), rest),
            rest => (None, rest),
        };
        let Some((params, body)) = rest.split_first() else {
            return Err(error("`(function name (params...) body...)' needs its parameters.", node));
        };
        write!(f, "function")?;
        if let Some(name) = name {
            write!(f, " {}", name.value)?;
        }
        Self::generate_params(f, params, indent)?;
        write!(f, " ")?;
        Self::generate_block(f, body, indent, true)
    }

    /// Parameters in parentheses, `(a (= b 1))` → `(a, b = 1)`.
    fn generate_params(f: Formatter, params: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
        let ParseNode::List { nodes, .. } = params else {
            return Err(error("Parameters are given as a list, e.g. `(a b)'.", params));
        };
        write!(f, "(")?;
        Self::generate_list(f, nodes, indent)?;
        write!(f, ")")?;
        Ok(())
    }

    /// Expressions separated by commas.
    fn generate_list(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
        for (index, node) in nodes.iter().enumerate() {
            if index > 0 {
                write!(f, ", ")?;
            }
            Self::generate_expression(f, node, indent, false)?;
        }
        Ok(())
    }

    /// Generate an expression. As an `operand` of an operator,
    /// an operation is put in parentheses.
    fn generate_expression(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>, operand: bool) -> Result<'a> {
        let nodes = match node {
            ParseNode::Symbol(atom) | ParseNode::Number(atom) | ParseNode::Raw(atom) => {
                write!(f, "{}", atom.value)?;
                return Ok(());
            },
            ParseNode::String(string) => {
                write_string(f, &string.value)?;
                return Ok(());
            },
            ParseNode::Attribute { .. } => return Err(error(
                "A keyword attribute can only be part of an object (a list of attributes).", node)),
            ParseNode::List { nodes, .. } => nodes,
        };
        let Some(first) = nodes.first() else {
            return Err(error("An empty list is not an expression, use `(array)' for an empty array.", node));
        };
        if first.is_attribute() {
            return Self::generate_object(f, nodes, indent);
        }
        let args = &nodes[1..];
        let keyword = head(node).unwrap_or_default();
        let parenthesise = |f: Formatter, open: bool| -> Result<'a> {
            if operand {
                write!(f, "{}", if open { "(" } else { ")" })?;
            }
            Ok(())
        };
        match (keyword, args) {
            (".", [object, keys @ ..]) if !keys.is_empty() => {
                Self::generate_expression(f, object, indent, true)?;
                for key in keys {
                    match key {
                        ParseNode::Symbol(key) if is_identifier(&key.value) => write!(f, ".{}", key.value)?,
                        _ => {
                            write!(f, "[")?;
                            Self::generate_expression(f, key, indent, false)?;
                            write!(f, "]")?;
                        },
                    }
                }
            },
            ("at", [object, index]) => {
                Self::generate_expression(f, object, indent, true)?;
                write!(f, "[")?;
                Self::generate_expression(f, index, indent, false)?;
                write!(f, "]")?;
            },
            ("array", items) => {
                write!(f, "[")?;
                Self::generate_list(f, items, indent)?;
                write!(f, "]")?;
            },
            ("new", [class, items @ ..]) => {
                write!(f, "new ")?;
                Self::generate_expression(f, class, indent, true)?;
                write!(f, "(")?;
                Self::generate_list(f, items, indent)?;
                write!(f, ")")?;
            },
            ("?", [condition, then, otherwise]) => {
                parenthesise(f, true)?;
                Self::generate_expression(f, condition, indent, true)?;
                write!(f, " ? ")?;
                Self::generate_expression(f, then, indent, true)?;
                write!(f, " : ")?;
                Self::generate_expression(f, otherwise, indent, true)?;
                parenthesise(f, false)?;
            },
            ("=>", [params, body @ ..]) if !body.is_empty() => {
                parenthesise(f, true)?;
                Self::generate_params(f, params, indent)?;
                write!(f, " => ")?;
                match body {
                    [ParseNode::List { nodes, .. }] if nodes.first().is_some_and(ParseNode::is_attribute) => {
                        write!(f, "(")?;
                        Self::generate_object(f, nodes, indent)?;
                        write!(f, ")")?;
                    },
                    [body] if !is_statement(body) => Self::generate_expression(f, body, indent, false)?,
                    body => Self::generate_block(f, body, indent, true)?,
                }
                parenthesise(f, false)?;
            },
            ("function", _) => {
                parenthesise(f, true)?;
                Self::generate_function(f, node, args, indent)?;
                parenthesise(f, false)?;
            },
            ("+" | "-", [value]) => {
                parenthesise(f, true)?;
                write!(f, "{keyword}")?;
                Self::generate_expression(f, value, indent, true)?;
                parenthesise(f, false)?;
            },
            (_, [value]) if UNARY.contains(&keyword) => {
                parenthesise(f, true)?;
                let space = if keyword.starts_with(char::is_alphabetic) { " " } else { "" };
                write!(f, "{keyword}{space}")?;
                Self::generate_expression(f, value, indent, true)?;
                parenthesise(f, false)?;
            },
            (_, [first, rest @ ..]) if BINARY.contains(&keyword) && !rest.is_empty() => {
                parenthesise(f, true)?;
                Self::generate_expression(f, first, indent, true)?;
                for operand in rest {
                    write!(f, " {keyword} ")?;
                    Self::generate_expression(f, operand, indent, true)?;
                }
                parenthesise(f, false)?;
            },
            _ if is_statement(node) => return Err(error(&format!(
                "`{keyword}' is a statement, not an expression{}.",
                if keyword == "if" { ", use `(? condition then else)' instead" } else { "" }), node)),
            _ if BINARY.contains(&keyword) || UNARY.contains(&keyword)
              || matches!(keyword, "." | "at" | "new" | "?" | "=>") => return Err(error(&format!(
                "Wrong number of operands given to `{keyword}'."), node)),
            // Otherwise, it is a call.
            _ => {
                Self::generate_expression(f, first, indent, true)?;
                write!(f, "(")?;
                Self::generate_list(f, args, indent)?;
                write!(f, ")")?;
            },
        }
        Ok(())
    }

    /// `(:a 1 :b 2)` → `{a: 1, b: 2}`.
    fn generate_object(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
        write!(f, "{{")?;
        for (index, node) in nodes.iter().enumerate() {
            let ParseNode::Attribute { keyword, node: value, .. } = node else {
                return Err(error("An object (a list of attributes) cannot also have plain items.", node));
            };
            write!(f, "{}", if index > 0 { ", " } else { "" })?;
            if is_identifier(keyword) {
                write!(f, "{keyword}")?;
            } else {
                write_string(f, keyword)?;
            }
            write!(f, ": ")?;
            Self::generate_expression(f, value, indent, false)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<'a> MarkupFormatter<'a> for JSFormatter<'a> {
    /// A document is indented, one statement per line.
    fn document(&self) -> std::result::Result<String, GenerationError<'a>> {
        let mut buf = String::new();
        Self::generate_statements(&mut buf, &self.tree, Some(0))?;
        Ok(buf)
    }

    /// Otherwise, it is compact, on one line.
    fn generate(&self, f: Formatter) -> std::result::Result<(), GenerationError<'a>> {
        Self::generate_statements(f, &self.tree, None)
    }
}
