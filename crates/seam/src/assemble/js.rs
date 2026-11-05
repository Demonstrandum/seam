//! Output JavaScript, written as s-expressions.
//! A list is a call, `(f a b)` → `f(a, b)`, unless it starts with an operator
//! or a keyword, e.g. `(+ a b)` → `a + b`, `(. a b)` → `a.b`,
//! `(const x 1)` → `const x = 1`, `(=> (x) (* x x))` → `(x) => x * x`.
//! Symbols and numbers are written as they are, and strings as JavaScript strings.
//! The whole syntax is described in `docs/javascript.md`.

use super::{MarkupFormatter, GenerationError, Formatter};
use super::json::write_string;
use crate::parse::parser::{ParseNode, ParseTree};

#[derive(Debug, Clone)]
pub struct JSFormatter<'a> {
    pub tree: ParseTree<'a>,
}

/// Operators written between any number of operands, `(+ a b c)` → `a + b + c`.
const BINARY: &[&str] = &[
    "+", "-", "*", "/", "%", "**",
    "&&", "||", "??", "&", "|", "^", "<<", ">>", ">>>",
];
/// Operators written between exactly two operands.
const BINARY_TWO: &[&str] = &[
    "==", "===", "!=", "!==", "<", ">", "<=", ">=", "in", "instanceof",
    "=", "+=", "-=", "*=", "/=", "%=", "**=", "&&=", "||=", "??=",
    "&=", "|=", "^=", "<<=", ">>=", ">>>=",
];
/// Operators written before their one operand, `(! a)` → `!a`
/// (`+` and `-` are too, when given one operand).
const UNARY: &[&str] = &["!", "~", "typeof", "void", "delete", "await", "++", "--", "..."];
/// Keywords that start statements, which are not expressions.
const STATEMENTS: &[&str] = &[
    "const", "let", "var", "using", "await-using",
    "if", "for", "for-await", "while", "do-while", "do", "switch", "try",
    "return", "throw", "break", "continue", "debugger", "with", "export", "//", "/*",
];
/// Keywords that start declarations, which can be exported.
const DECLARATIONS: &[&str] = &[
    "const", "let", "var", "using", "await-using", "function", "function*", "class", "async",
];
/// Forms that are expressions, but written with their own syntax.
const EXPRESSIONS: &[&str] = &[
    ".", "?.", "[]", "array", "object", "regex", "`", "new", "?", ",", "=>",
    "function", "function*", "async", "class", "++post", "--post", "yield", "yield*",
];

type Result<'a> = std::result::Result<(), GenerationError<'a>>;

fn error<'a>(message: &str, node: &ParseNode<'a>) -> GenerationError<'a> {
    GenerationError::new("JavaScript", message, node.site())
}

/// A symbol, unless it is escaped as a name, `\array`.
/// `+` and `-` and the like are read as numbers, so they are too.
fn word<'n>(node: &'n ParseNode) -> Option<&'n str> {
    match node {
        ParseNode::Symbol(symbol) if !(symbol.is_escaped() && is_identifier(&symbol.value)) => Some(&symbol.value),
        ParseNode::Number(number) if number.value.parse::<f64>().is_err()
            && !number.value.starts_with(|c: char| c.is_ascii_digit()) => Some(&number.value),
        _ => None,
    }
}

/// Whether a node is the given word.
fn is_word(node: &ParseNode, expected: &str) -> bool {
    word(node) == Some(expected)
}

/// The keyword or operator a list starts with.
fn head<'n>(node: &'n ParseNode) -> Option<&'n str> {
    node.list().and_then(|nodes| nodes.first()).and_then(word)
}

/// The arguments of a list, after its head.
fn arguments<'n, 'a>(node: &'n ParseNode<'a>) -> &'n [ParseNode<'a>] {
    node.list().map_or(&[], |nodes| nodes.get(1..).unwrap_or_default())
}

/// Whether a node is a statement, and not an expression.
fn is_statement(node: &ParseNode) -> bool {
    let args = arguments(node);
    match head(node) {
        Some(keyword) if STATEMENTS.contains(&keyword) => true,
        Some(label) if label.len() > 1 && label.ends_with(':') => true,
        Some("import") => args.iter().any(|arg| is_word(arg, "from")),
        Some("function" | "function*" | "class") => matches!(args.first(), Some(ParseNode::Symbol(_))),
        Some("async") => args.first().is_some_and(is_statement),
        _ => false,
    }
}

/// Whether a list is a pattern or a value written in brackets or braces.
fn is_pattern(node: &ParseNode) -> bool {
    matches!(head(node), Some("array" | "object"))
}

/// Whether a key can be written without quotes, `{a: 1}` and `x.a`.
fn is_identifier(key: &str) -> bool {
    let mut chars = key.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_' || c == '$')
        && chars.all(|c| c.is_alphanumeric() || c == '_' || c == '$')
}

/// Whether an expression is written without any operator outside of
/// brackets, so it needs no parentheses as an operand.
fn is_primary(node: &ParseNode) -> bool {
    match node {
        ParseNode::List { nodes, .. } => match head(node) {
            Some("." | "?." | "[]" | "array" | "object" | "regex" | "`") => true,
            Some(keyword) => !(BINARY.contains(&keyword) || BINARY_TWO.contains(&keyword)
                || UNARY.contains(&keyword) || EXPRESSIONS.contains(&keyword)
                || STATEMENTS.contains(&keyword)),
            // An object of attributes, or a call.
            None => !nodes.is_empty(),
        },
        ParseNode::Number(number) => !number.value.starts_with(['-', '+']),
        _ => true,
    }
}

/// Whether an expression has no calls, so it can be the class of `new`.
fn is_constructor(node: &ParseNode) -> bool {
    match node {
        ParseNode::List { nodes, .. } => matches!(head(node), Some("." | "[]"))
            && nodes[1..].iter().all(is_constructor),
        _ => true,
    }
}

impl<'a> JSFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }
}

/// Start a new line at an indentation level, when pretty-printing,
/// or else separate with a space.
fn newline(f: Formatter, indent: Option<usize>) -> std::fmt::Result {
    match indent {
        Some(indent) => write!(f, "\n{:width$}", "", width = 2 * indent),
        None => write!(f, " "),
    }
}

fn deeper(indent: Option<usize>) -> Option<usize> {
    indent.map(|indent| indent + 1)
}

/// Generate statements, one after another.
fn statements<'a>(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
    for (index, node) in nodes.iter().enumerate() {
        if index > 0 {
            newline(f, indent)?;
        }
        statement(f, node, indent)?;
    }
    Ok(())
}

/// Generate a block of statements in braces. With `returns`, the last
/// expression is returned, as it is the result of a function.
fn block<'a>(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>, returns: bool) -> Result<'a> {
    write!(f, "{{")?;
    let inner = deeper(indent);
    for (index, node) in nodes.iter().enumerate() {
        newline(f, inner)?;
        if returns && index + 1 == nodes.len() && !is_statement(node) {
            write!(f, "return ")?;
            expression(f, node, inner)?;
            write!(f, ";")?;
        } else {
            statement(f, node, inner)?;
        }
    }
    if !nodes.is_empty() {
        newline(f, indent)?;
    }
    write!(f, "}}")?;
    Ok(())
}

/// A body of a statement: a block from `(do ...)`, or a single statement in braces.
fn branch<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    if head(node) == Some("do") {
        block(f, arguments(node), indent, false)
    } else {
        block(f, std::slice::from_ref(node), indent, false)
    }
}

fn statement<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let Some(keyword) = head(node) else {
        return expression_statement(f, node, indent);
    };
    let args = arguments(node);
    match (keyword, args) {
        ("const" | "let" | "var" | "using" | "await-using", _) => {
            declaration(f, node, indent)?;
            write!(f, ";")?;
        },
        ("if", [condition, then, otherwise @ ..]) => {
            write!(f, "if (")?;
            expression(f, condition, indent)?;
            write!(f, ") ")?;
            branch(f, then, indent)?;
            match otherwise {
                [] => {},
                [otherwise] => {
                    write!(f, " else ")?;
                    if head(otherwise) == Some("if") {
                        statement(f, otherwise, indent)?;
                    } else {
                        branch(f, otherwise, indent)?;
                    }
                },
                _ => return Err(error("`(if condition then else)' takes at most one else branch, \
                                       use `(do ...)' for more statements.", node)),
            }
        },
        ("for" | "for-await", [binding, of, iterable, body @ ..])
            if is_word(of, "of") || (keyword == "for" && is_word(of, "in")) => {
            write!(f, "{} (", if keyword == "for" { "for" } else { "for await" })?;
            if let Some("const" | "let" | "var" | "using" | "await-using") = head(binding) {
                declaration(f, binding, indent)?;
            } else {
                write!(f, "const ")?;
                expression(f, binding, indent)?;
            }
            write!(f, " {} ", word(of).unwrap_or_default())?;
            expression(f, iterable, indent)?;
            write!(f, ") ")?;
            block(f, body, indent, false)?;
        },
        ("for", [init, test, update, body @ ..]) => {
            write!(f, "for (")?;
            match init {
                ParseNode::List { nodes, .. } if nodes.is_empty() => {},
                _ if matches!(head(init), Some("const" | "let" | "var")) => declaration(f, init, indent)?,
                _ => expression(f, init, indent)?,
            }
            for part in [test, update] {
                write!(f, ";")?;
                if !matches!(part, ParseNode::List { nodes, .. } if nodes.is_empty()) {
                    write!(f, " ")?;
                    expression(f, part, indent)?;
                }
            }
            write!(f, ") ")?;
            block(f, body, indent, false)?;
        },
        ("while", [condition, body @ ..]) => {
            write!(f, "while (")?;
            expression(f, condition, indent)?;
            write!(f, ") ")?;
            block(f, body, indent, false)?;
        },
        ("do-while", [condition, body @ ..]) => {
            write!(f, "do ")?;
            block(f, body, indent, false)?;
            write!(f, " while (")?;
            expression(f, condition, indent)?;
            write!(f, ");")?;
        },
        ("do", body) => block(f, body, indent, false)?,
        ("switch", [value, clauses @ ..]) => {
            write!(f, "switch (")?;
            expression(f, value, indent)?;
            write!(f, ") {{")?;
            let inner = deeper(indent);
            for clause in clauses {
                newline(f, inner)?;
                let body = match (head(clause), arguments(clause)) {
                    (Some("case"), [value, body @ ..]) => {
                        write!(f, "case ")?;
                        expression(f, value, inner)?;
                        body
                    },
                    (Some("default"), body) => {
                        write!(f, "default")?;
                        body
                    },
                    _ => return Err(error("A `switch' has only `(case value body...)' \
                                           and `(default body...)' clauses.", clause)),
                };
                write!(f, ":")?;
                for node in body {
                    newline(f, deeper(inner))?;
                    statement(f, node, deeper(inner))?;
                }
            }
            newline(f, indent)?;
            write!(f, "}}")?;
        },
        ("try", _) => {
            let handlers = args.iter().rev()
                .take_while(|node| matches!(head(node), Some("catch" | "finally")))
                .count();
            let (body, handlers) = args.split_at(args.len() - handlers);
            if handlers.is_empty() {
                return Err(error("`(try body... (catch e ...) (finally ...))' needs a `catch' or `finally'.", node));
            }
            write!(f, "try ")?;
            block(f, body, indent, false)?;
            for handler in handlers {
                match (head(handler), arguments(handler)) {
                    (Some("catch"), [binding, body @ ..]) => {
                        write!(f, " catch ")?;
                        if !matches!(binding, ParseNode::List { nodes, .. } if nodes.is_empty()) {
                            write!(f, "(")?;
                            expression(f, binding, indent)?;
                            write!(f, ") ")?;
                        }
                        block(f, body, indent, false)?;
                    },
                    (Some("finally"), body) => {
                        write!(f, " finally ")?;
                        block(f, body, indent, false)?;
                    },
                    _ => return Err(error("`(catch binding body...)' needs a binding, \
                                           or `()' for none.", handler)),
                }
            }
        },
        ("return" | "throw", [value]) => {
            write!(f, "{keyword} ")?;
            expression(f, value, indent)?;
            write!(f, ";")?;
        },
        ("return" | "break" | "continue" | "debugger", []) => write!(f, "{keyword};")?,
        ("break" | "continue", [label @ ParseNode::Symbol(_)]) => {
            write!(f, "{keyword} ")?;
            expression(f, label, indent)?;
            write!(f, ";")?;
        },
        ("with", [object, body @ ..]) => {
            write!(f, "with (")?;
            expression(f, object, indent)?;
            write!(f, ") ")?;
            block(f, body, indent, false)?;
        },
        (label, body) if label.len() > 1 && label.ends_with(':') => {
            write!(f, "{label} ")?;
            match body {
                [statement_] => statement(f, statement_, indent)?,
                body => block(f, body, indent, false)?,
            }
        },
        ("//" | "/*", text) => {
            let text = text.iter().map(text_of).collect::<Vec<_>>().join(" ");
            if keyword == "//" {
                for (index, line) in text.lines().enumerate() {
                    if index > 0 {
                        newline(f, indent)?;
                    }
                    write!(f, "// {line}")?;
                }
                // A line comment must end its line, even when compact.
                if indent.is_none() {
                    writeln!(f)?;
                }
            } else {
                write!(f, "/* {} */", text.replace("*/", "*\\/"))?;
            }
        },
        ("import", [source @ ParseNode::String(_), rest @ ..]) => {
            write!(f, "import ")?;
            expression(f, source, indent)?;
            import_attributes(f, rest, indent)?;
            write!(f, ";")?;
        },
        ("import" | "export", _) if args.iter().any(|arg| is_word(arg, "from")) => {
            write!(f, "{keyword} ")?;
            module_clause(f, node, args, indent)?;
            write!(f, ";")?;
        },
        ("export", [default, value]) if is_word(default, "default") => {
            write!(f, "export default ")?;
            if is_statement(value) {
                statement(f, value, indent)?;
            } else {
                expression(f, value, indent)?;
                write!(f, ";")?;
            }
        },
        ("export", [declaration_]) if head(declaration_).is_some_and(|head| DECLARATIONS.contains(&head)) => {
            write!(f, "export ")?;
            statement(f, declaration_, indent)?;
        },
        ("export", [names @ ParseNode::List { .. }]) => {
            write!(f, "export ")?;
            module_clause(f, node, std::slice::from_ref(names), indent)?;
            write!(f, ";")?;
        },
        ("function" | "function*" | "class", [ParseNode::Symbol(_), ..]) => expression(f, node, indent)?,
        ("async", [inner]) if is_statement(inner) => expression(f, node, indent)?,
        _ if is_statement(node) => return Err(error(&format!("Malformed `{keyword}' statement."), node)),
        _ => expression_statement(f, node, indent)?,
    }
    Ok(())
}

/// An expression as a statement, in parentheses if it would
/// otherwise read as a block or a declaration.
fn expression_statement<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let mut buffer = String::new();
    expression(&mut buffer, node, indent)?;
    let ambiguous = buffer.starts_with('{') || buffer.starts_with("let [")
        || ["function", "class", "async function"].iter().any(|word| {
            buffer.strip_prefix(word).is_some_and(|rest| !rest.starts_with(|c: char| c.is_alphanumeric() || c == '_' || c == '$'))
        });
    if ambiguous {
        write!(f, "({buffer});")?;
    } else {
        write!(f, "{buffer};")?;
    }
    Ok(())
}

/// The text of a comment.
fn text_of(node: &ParseNode) -> String {
    match node {
        ParseNode::String(atom) | ParseNode::Symbol(atom) | ParseNode::Number(atom) | ParseNode::Raw(atom) => atom.value.to_string(),
        _ => String::new(),
    }
}

/// `(const x 1)`, `(let (a 1) (b))`, without the semicolon.
fn declaration<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let keyword = head(node).unwrap_or_default();
    let args = arguments(node);
    write!(f, "{} ", if keyword == "await-using" { "await using" } else { keyword })?;
    let declarator = |f: Formatter, nodes: &[ParseNode<'a>]| -> Result<'a> {
        match nodes {
            [name] => expression(f, name, indent),
            [name, value] => {
                expression(f, name, indent)?;
                write!(f, " = ")?;
                expression(f, value, indent)
            },
            _ => Err(error(&format!("`({keyword} name value)' takes a name and at most one value."), node)),
        }
    };
    match args {
        [ParseNode::List { .. }, ..] if !is_pattern(&args[0]) => {
            for (index, pair) in args.iter().enumerate() {
                if index > 0 {
                    write!(f, ", ")?;
                }
                let ParseNode::List { nodes, .. } = pair else {
                    return Err(error(&format!("Each of several declarations is a list, \
                                               `({keyword} (a 1) (b 2))'."), pair));
                };
                declarator(f, nodes)?;
            }
            Ok(())
        },
        [] => Err(error(&format!("`({keyword} name value)' needs a name."), node)),
        args => declarator(f, args),
    }
}

/// The words of an import or export, `D ({} a (as b c)) from "x"`.
fn module_clause<'a>(f: Formatter, node: &ParseNode<'a>, args: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
    let from = args.iter().position(|arg| is_word(arg, "from")).unwrap_or(args.len());
    for (index, part) in args[..from].iter().enumerate() {
        if index > 0 {
            write!(f, ", ")?;
        }
        match part {
            ParseNode::List { nodes, .. } if head(part) == Some("as") => specifier(f, part, &nodes[1..])?,
            ParseNode::List { nodes, .. } => {
                write!(f, "{{")?;
                for (index, name) in nodes.iter().enumerate() {
                    write!(f, "{}", if index > 0 { ", " } else { "" })?;
                    match name {
                        ParseNode::List { nodes, .. } if head(name) == Some("as") => specifier(f, name, &nodes[1..])?,
                        name => module_name(f, name)?,
                    }
                }
                write!(f, "}}")?;
            },
            part => module_name(f, part)?,
        }
    }
    if let Some(rest) = args.get(from..).filter(|rest| !rest.is_empty()) {
        let [_, source, attributes @ ..] = rest else {
            return Err(error("`from' needs the module to come from.", node));
        };
        write!(f, " from ")?;
        expression(f, source, indent)?;
        import_attributes(f, attributes, indent)?;
    }
    Ok(())
}

/// `(as a b)` → `a as b`.
fn specifier<'a>(f: Formatter, node: &ParseNode<'a>, names: &[ParseNode<'a>]) -> Result<'a> {
    let [name, alias] = names else {
        return Err(error("`(as name alias)' takes a name and an alias.", node));
    };
    module_name(f, name)?;
    write!(f, " as ")?;
    module_name(f, alias)
}

/// A name in an import or export, which may be a string.
fn module_name<'a>(f: Formatter, node: &ParseNode<'a>) -> Result<'a> {
    match node {
        ParseNode::String(name) => write_string(f, &name.value)?,
        ParseNode::Symbol(name) | ParseNode::Number(name) => write!(f, "{}", name.value)?,
        _ => return Err(error("Expected a name to import or export.", node)),
    }
    Ok(())
}

/// `:with (:type "json")` → ` with {type: "json"}`.
fn import_attributes<'a>(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
    for node in nodes {
        match node {
            ParseNode::Attribute { keyword, node: value, .. } if keyword == "with" => {
                write!(f, " with ")?;
                expression(f, value, indent)?;
            },
            _ => return Err(error("Only `:with (:key value)' can come after the module.", node)),
        }
    }
    Ok(())
}

/// `(function name? (params...) body...)`, returning its last expression.
fn function<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let keyword = head(node).unwrap_or_default();
    let (name, rest) = match arguments(node) {
        [ParseNode::Symbol(name), rest @ ..] => (Some(name), rest),
        rest => (None, rest),
    };
    let Some((params, body)) = rest.split_first() else {
        return Err(error(&format!("`({keyword} name (params...) body...)' needs its parameters."), node));
    };
    write!(f, "{keyword}")?;
    if let Some(name) = name {
        write!(f, " {}", name.value)?;
    }
    parameters(f, params, indent)?;
    write!(f, " ")?;
    // A generator's result is what it yields, so it returns nothing itself.
    block(f, body, indent, keyword == "function")
}

/// Parameters in parentheses, `(a (= b 1))` → `(a, b = 1)`.
fn parameters<'a>(f: Formatter, params: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let ParseNode::List { nodes, .. } = params else {
        return Err(error("Parameters are given as a list, e.g. `(a b)'.", params));
    };
    write!(f, "(")?;
    list(f, nodes, indent)?;
    write!(f, ")")?;
    Ok(())
}

/// Expressions separated by commas.
fn list<'a>(f: Formatter, nodes: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
    for (index, node) in nodes.iter().enumerate() {
        if index > 0 {
            write!(f, ", ")?;
        }
        expression(f, node, indent)?;
    }
    Ok(())
}

/// Generate an expression as an operand, in parentheses unless it is primary.
fn operand<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    if is_primary(node) {
        expression(f, node, indent)
    } else {
        write!(f, "(")?;
        expression(f, node, indent)?;
        write!(f, ")")?;
        Ok(())
    }
}

/// A computed key, `([] k)`, of a property or a method.
fn computed<'n, 'a>(node: &'n ParseNode<'a>) -> Option<&'n ParseNode<'a>> {
    match (head(node), arguments(node)) {
        (Some("[]"), [key]) => Some(key),
        _ => None,
    }
}

/// Generate an expression.
fn expression<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
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
        return Err(error("An empty list is not an expression, use `(array)' for an empty array \
                          (`()' is only a hole in an array or an empty part of a `for').", node));
    };
    if first.is_attribute() {
        return object(f, nodes, indent);
    }
    let args = &nodes[1..];
    let keyword = head(node).unwrap_or_default();
    match (keyword, args) {
        ("." | "?.", [object, keys @ ..]) if !keys.is_empty() => {
            let dot = if keyword == "." { "." } else { "?." };
            operand(f, object, indent)?;
            for key in keys {
                match (key, computed(key)) {
                    (ParseNode::Symbol(name), _) if is_identifier(&name.value) || name.value.starts_with('#') =>
                        write!(f, "{dot}{}", name.value)?,
                    (_, Some(key)) | (key, None) => {
                        write!(f, "{}[", if keyword == "." { "" } else { "?." })?;
                        expression(f, key, indent)?;
                        write!(f, "]")?;
                    },
                }
            }
        },
        ("[]", [object, keys @ ..]) if !keys.is_empty() => {
            operand(f, object, indent)?;
            for key in keys {
                write!(f, "[")?;
                expression(f, key, indent)?;
                write!(f, "]")?;
            }
        },
        ("array", items) => {
            write!(f, "[")?;
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    write!(f, ", ")?;
                }
                match item {
                    // A hole.
                    ParseNode::List { nodes, .. } if nodes.is_empty() => {
                        if index + 1 == items.len() {
                            write!(f, ",")?;
                        }
                    },
                    item => expression(f, item, indent)?,
                }
            }
            write!(f, "]")?;
        },
        ("object", entries) => object(f, entries, indent)?,
        ("regex", [pattern, flags @ ..]) if flags.len() <= 1 => {
            let pattern = text_of(pattern);
            write!(f, "/")?;
            if pattern.is_empty() {
                write!(f, "(?:)")?;
            }
            let mut escaped = false;
            let mut class = false;
            for c in pattern.chars() {
                match c {
                    '\n' => write!(f, "\\n")?,
                    '\r' => write!(f, "\\r")?,
                    '/' if !escaped && !class => write!(f, "\\/")?,
                    c => write!(f, "{c}")?,
                }
                if !escaped {
                    class = match c { '[' => true, ']' => false, _ => class };
                }
                escaped = c == '\\' && !escaped;
            }
            write!(f, "/")?;
            if let Some(flags) = flags.first() {
                write!(f, "{}", text_of(flags))?;
            }
        },
        ("`", parts) => {
            let parts = match parts {
                [ParseNode::Attribute { keyword, node: tag, .. }, parts @ ..] if keyword == "tag" => {
                    operand(f, tag, indent)?;
                    parts
                },
                parts => parts,
            };
            write!(f, "`")?;
            for part in parts {
                if let ParseNode::String(text) = part {
                    let mut chars = text.value.chars().peekable();
                    while let Some(c) = chars.next() {
                        match c {
                            '`' | '\\' => write!(f, "\\{c}")?,
                            '$' if chars.peek() == Some(&'{') => write!(f, "\\$")?,
                            c => write!(f, "{c}")?,
                        }
                    }
                } else {
                    write!(f, "${{")?;
                    expression(f, part, indent)?;
                    write!(f, "}}")?;
                }
            }
            write!(f, "`")?;
        },
        ("new", [class, items @ ..]) => {
            write!(f, "new ")?;
            if is_constructor(class) && is_primary(class) {
                expression(f, class, indent)?;
            } else {
                write!(f, "(")?;
                expression(f, class, indent)?;
                write!(f, ")")?;
            }
            write!(f, "(")?;
            list(f, items, indent)?;
            write!(f, ")")?;
        },
        ("?", [condition, then, otherwise]) => {
            operand(f, condition, indent)?;
            write!(f, " ? ")?;
            operand(f, then, indent)?;
            write!(f, " : ")?;
            operand(f, otherwise, indent)?;
        },
        (",", items) if !items.is_empty() => {
            write!(f, "(")?;
            list(f, items, indent)?;
            write!(f, ")")?;
        },
        ("=>", [params, body @ ..]) if !body.is_empty() => {
            parameters(f, params, indent)?;
            write!(f, " => ")?;
            match body {
                [body] if body.list().is_some_and(|nodes| nodes.first().is_some_and(ParseNode::is_attribute))
                    || head(body) == Some("object") => {
                    write!(f, "(")?;
                    expression(f, body, indent)?;
                    write!(f, ")")?;
                },
                [body] if !is_statement(body) => expression(f, body, indent)?,
                body => block(f, body, indent, true)?,
            }
        },
        ("function" | "function*", _) => function(f, node, indent)?,
        ("async", [inner]) if matches!(head(inner), Some("function" | "function*" | "=>")) => {
            write!(f, "async ")?;
            expression(f, inner, indent)?;
        },
        ("class", _) => class(f, node, indent)?,
        ("+" | "-", [value]) => {
            write!(f, "{keyword}")?;
            operand(f, value, indent)?;
        },
        ("++post" | "--post", [value]) => {
            operand(f, value, indent)?;
            write!(f, "{}", &keyword[..2])?;
        },
        ("yield" | "yield*", []) if keyword == "yield" => write!(f, "yield")?,
        ("yield" | "yield*", [value]) => {
            write!(f, "{keyword} ")?;
            operand(f, value, indent)?;
        },
        (_, [value]) if UNARY.contains(&keyword) => {
            let space = if keyword.starts_with(char::is_alphabetic) { " " } else { "" };
            write!(f, "{keyword}{space}")?;
            operand(f, value, indent)?;
        },
        (_, [first, rest @ ..]) if (BINARY.contains(&keyword) && !rest.is_empty())
                                || (BINARY_TWO.contains(&keyword) && rest.len() == 1) => {
            operand(f, first, indent)?;
            for value in rest {
                write!(f, " {keyword} ")?;
                operand(f, value, indent)?;
            }
        },
        _ if is_statement(node) => return Err(error(&format!(
            "`{keyword}' is a statement, not an expression{}.",
            if keyword == "if" { ", use `(? condition then else)' instead" } else { "" }), node)),
        _ if BINARY.contains(&keyword) || BINARY_TWO.contains(&keyword)
          || UNARY.contains(&keyword) || EXPRESSIONS.contains(&keyword) => return Err(error(&format!(
            "Wrong number of operands given to `{keyword}'."), node)),
        // `(f?. x)` → `f?.(x)`.
        (callee, _) if callee.len() > 2 && callee.ends_with("?.") => {
            write!(f, "{callee}(")?;
            list(f, args, indent)?;
            write!(f, ")")?;
        },
        // Otherwise, it is a call.
        _ => {
            operand(f, first, indent)?;
            write!(f, "(")?;
            list(f, args, indent)?;
            write!(f, ")")?;
        },
    }
    Ok(())
}

/// A key of a property, method or field.
fn key<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    match (node, computed(node)) {
        (ParseNode::Symbol(name) | ParseNode::Number(name), _) => write!(f, "{}", name.value)?,
        (ParseNode::String(name), _) => write_string(f, &name.value)?,
        (_, Some(key)) => {
            write!(f, "[")?;
            expression(f, key, indent)?;
            write!(f, "]")?;
        },
        _ => return Err(error("A key is a name, a string, or `([] key)' for a computed key.", node)),
    }
    Ok(())
}

/// A key written by a keyword attribute, quoted if it is not a name.
fn keyword_key(f: Formatter, keyword: &str) -> std::fmt::Result {
    if is_identifier(keyword) || keyword.strip_prefix('#').is_some_and(is_identifier) {
        write!(f, "{keyword}")
    } else {
        write_string(f, keyword)
    }
}

/// `(object :a 1 b (... c) (key k v) (m () ...))` → `{a: 1, b, ...c, [k]: v, m() {...}}`.
fn object<'a>(f: Formatter, entries: &[ParseNode<'a>], indent: Option<usize>) -> Result<'a> {
    write!(f, "{{")?;
    for (index, entry) in entries.iter().enumerate() {
        write!(f, "{}", if index > 0 { ", " } else { "" })?;
        match (entry, head(entry), arguments(entry)) {
            (ParseNode::Attribute { keyword, node: value, .. }, _, _) => {
                keyword_key(f, keyword)?;
                write!(f, ": ")?;
                expression(f, value, indent)?;
            },
            (ParseNode::Symbol(name), _, _) => write!(f, "{}", name.value)?,
            (_, Some("..." | "="), _) => expression(f, entry, indent)?,
            (_, Some("key"), [name, value]) => {
                write!(f, "[")?;
                expression(f, name, indent)?;
                write!(f, "]: ")?;
                expression(f, value, indent)?;
            },
            (ParseNode::List { .. }, _, _) => method(f, entry, indent)?,
            _ => return Err(error("An entry of an object is `:key value', a name, `(... value)', \
                                   `(key k value)' or a method.", entry)),
        }
    }
    write!(f, "}}")?;
    Ok(())
}

/// A method of an object or class, `(name (params...) body...)`, with
/// `get`, `set`, `async` and `*` before it.
fn method<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let nodes: &[ParseNode<'a>] = node.list().map_or(&[], |nodes| nodes);
    match (head(node), nodes) {
        (Some(kind @ ("get" | "set")), [_, name, ParseNode::List { .. }, ..]) if !matches!(name, ParseNode::List { .. }) || computed(name).is_some() => {
            write!(f, "{kind} ")?;
            method_body(f, node, name, &nodes[2], &nodes[3..], indent, kind == "get")
        },
        (Some("async"), [_, inner]) => {
            write!(f, "async ")?;
            method(f, inner, indent)
        },
        (Some("*"), [_, name, params, body @ ..]) => {
            write!(f, "*")?;
            method_body(f, node, name, params, body, indent, false)
        },
        (_, [name, params @ ParseNode::List { .. }, body @ ..]) => {
            let returns = !matches!(name, ParseNode::Symbol(name) if name.value == "constructor");
            method_body(f, node, name, params, body, indent, returns)
        },
        _ => Err(error("A method is `(name (params...) body...)'.", node)),
    }
}

fn method_body<'a>(f: Formatter, node: &ParseNode<'a>, name: &ParseNode<'a>, params: &ParseNode<'a>,
                   body: &[ParseNode<'a>], indent: Option<usize>, returns: bool) -> Result<'a> {
    if !matches!(params, ParseNode::List { .. }) {
        return Err(error("A method is `(name (params...) body...)'.", node));
    }
    key(f, name, indent)?;
    parameters(f, params, indent)?;
    write!(f, " ")?;
    block(f, body, indent, returns)
}

/// `(class Name? :extends Base members...)`.
fn class<'a>(f: Formatter, node: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    let mut members = arguments(node);
    write!(f, "class")?;
    if let [ParseNode::Symbol(name), rest @ ..] = members {
        write!(f, " {}", name.value)?;
        members = rest;
    }
    if let [ParseNode::Attribute { keyword, node: base, .. }, rest @ ..] = members && keyword == "extends" {
        write!(f, " extends ")?;
        operand(f, base, indent)?;
        members = rest;
    }
    write!(f, " {{")?;
    let inner = deeper(indent);
    for member in members {
        newline(f, inner)?;
        class_member(f, member, inner)?;
    }
    if !members.is_empty() {
        newline(f, indent)?;
    }
    write!(f, "}}")?;
    Ok(())
}

fn class_member<'a>(f: Formatter, member: &ParseNode<'a>, indent: Option<usize>) -> Result<'a> {
    match (member, head(member), arguments(member)) {
        (ParseNode::Attribute { keyword, node: value, .. }, _, _) => {
            keyword_key(f, keyword)?;
            write!(f, " = ")?;
            expression(f, value, indent)?;
            write!(f, ";")?;
        },
        (_, Some("field"), [name, value @ ..]) if value.len() <= 1 => {
            key(f, name, indent)?;
            if let [value] = value {
                write!(f, " = ")?;
                expression(f, value, indent)?;
            }
            write!(f, ";")?;
        },
        (_, Some("static"), [static_block]) if head(static_block) == Some("do") => {
            write!(f, "static ")?;
            block(f, arguments(static_block), indent, false)?;
        },
        (_, Some("static"), members) if !members.is_empty() => {
            for (index, inner) in members.iter().enumerate() {
                if index > 0 {
                    newline(f, indent)?;
                }
                write!(f, "static ")?;
                class_member(f, inner, indent)?;
            }
        },
        (ParseNode::List { .. }, _, _) => method(f, member, indent)?,
        _ => return Err(error("A member of a class is `:field value', `(field name)', \
                               a method, or `(static member)'.", member)),
    }
    Ok(())
}

impl<'a> MarkupFormatter<'a> for JSFormatter<'a> {
    /// A document is indented, one statement per line.
    fn document(&self) -> std::result::Result<String, GenerationError<'a>> {
        let mut buf = String::new();
        statements(&mut buf, &self.tree, Some(0))?;
        Ok(buf)
    }

    /// Otherwise, it is compact, on one line.
    fn generate(&self, f: Formatter) -> std::result::Result<(), GenerationError<'a>> {
        statements(f, &self.tree, None)
    }
}
