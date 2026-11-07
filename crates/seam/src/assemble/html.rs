//! Assembles an expanded tree into valid HTML.

use super::{child_whitespace, write_escaped, Escaping, GenerationError, MarkupFormatter, Formatter};
use super::{
    text::PlainTextFormatter,
    xml::XMLFormatter,
    json,
    js::JSFormatter,
    css::{self, CSSFormatter},
};

use crate::parse::parser::{ParseNode, ParseTree};
use crate::parse::tokens;
use std::{borrow::Cow, fmt::Write};

#[derive(Debug, Clone)]
pub struct HTMLFormatter<'a> {
    pub tree: ParseTree<'a>,
}

impl<'a> HTMLFormatter<'a> {
    #[must_use]
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree
        }
    }

    /// Generate a sequence of nodes.
    pub fn generate_nodes(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for node in nodes {
            Self::generate_html_node(f, node, node.leading_whitespace())?;
        }
        Ok(())
    }

    /// Generate the children of an element (see [`child_whitespace`]).
    pub fn generate_children(f: Formatter, nodes: &[ParseNode<'a>]) -> Result<(), GenerationError<'a>> {
        for (index, node) in nodes.iter().enumerate() {
            Self::generate_html_node(f, node, child_whitespace(index, node))?;
        }
        Ok(())
    }

    /// Write the attributes at the start of `nodes`, returning the nodes after them.
    fn generate_attributes<'n>(f: Formatter, mut nodes: &'n [ParseNode<'a>])
    -> Result<&'n [ParseNode<'a>], GenerationError<'a>> {
        while let Some(ParseNode::Attribute { node, keyword, leading_whitespace, .. }) = nodes.first() {
            let leading_whitespace = if leading_whitespace.is_empty() { " " } else { leading_whitespace };
            write!(f, "{leading_whitespace}{keyword}=\"")?;
            write_escaped(f, &attribute_value(node)?)?;
            write!(f, "\"")?;
            nodes = &nodes[1..];
        }
        Ok(nodes)
    }

    /// Generate a node, preceded by the given `leading` whitespace.
    fn generate_html_node(f: Formatter, node: &ParseNode<'a>, leading: &str) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
            | ParseNode::Number(node)
            | ParseNode::String(node) => {
                write!(f, "{leading}")?;
                write_escaped(f, &node.value)?;
            },
            ParseNode::Raw(node) => {
                // Don't escape any symbols in a raw-content string.
                write!(f, "{leading}")?;
                write!(f, "{}", node.value)?;
            },
            ParseNode::List { nodes: list, end_token, .. } => {
                write!(f, "{leading}")?;
                let head = list.first();
                let tag: &str;  // html <tag> name.
                if let Some(head_node) = head {
                    if let ParseNode::Symbol(head_symbol) = head_node {
                        tag = &head_symbol.value;
                        write!(f, "<{tag}")?;
                    } else {
                        // Error, tags can only have symbol values.
                        return Err(GenerationError::new("HTML",
                            "HTML tags can only be given as symbols.",
                            head_node.site()));
                    }
                } else {
                    // Error, empty tags not supported.
                    return Err(GenerationError::new("HTML",
                        "Empty lists cannot be converted into a valid HTML tag.",
                        node.site()));
                }
                let tag = tag.to_ascii_lowercase();

                let mut rest = &list[1..];

                // Declarations behave differently.
                if tag.as_bytes()[0] == b'!' {
                    while !rest.is_empty() {
                        if let Some(node) = rest[0].symbolic() {
                            write!(f, " {}", node.value)?;
                        } else {
                            return Err(GenerationError::new("HTML",
                                "Non-symbolic item in declaration",
                                rest[0].site()));
                        }
                        rest = &rest[1..];
                    }
                    write!(f, ">")?;
                    return Ok(());
                }

                let rest = Self::generate_attributes(f, rest)?;
                write!(f, ">")?;

                // Check early if this tag is a void element.
                if VOID_ELEMENTS.binary_search(&tag.as_str()).is_ok() {
                    // Void elements cannot have children.
                    if let Some(child_node) = rest.first() {
                        return Err(GenerationError::new("HTML",
                            &format!("A void element such as `<{tag}>' cannot have children."),
                            child_node.site()));
                    }
                    // Finished: void elements don't get a closing tag.
                    return Ok(());
                }

                // The first node to a tag should have its whitespace supressed!
                // e.g. `(p hello world)` -> `<p>hello world</p>`.
                // But if there's a new line, its likely it should be carreid through.
                // e.g.
                // ```
                // (div
                //    hello)
                // ```
                // ->
                // ```
                // <div>
                //    hello
                // </div>
                let is_first_node_on_next_line = rest.first()
                    .is_some_and(|first| first.leading_whitespace().contains('\n'));

                // Handle tags which *do not* contain HTML as syntax:
                //    <pre>, <style>, <script>, <math>, <svg>, <textarea>, <title>
                // Specifically:
                //   - <svg> and <math> contain XML, not HTML;
                //   - <pre>, <textarea> and <title> contain raw text, not parsed as HTML;
                //   - <pre> will display raw text found in source code;
                //   - <textarea> and <title> however, are escapable (evaluate macros);
                //   - <script> contains JavaScript or JSON, which we generate (see [`script_language`]);
                //   - <style> contains CSS, which we have our own parser for already.
                match tag.as_str() {
                    "pre" => {
                        let mut escaped = Escaping(f);
                        match verbatim_text(list, end_token) {
                            // <pre> preserves the text as written in the *source* file.
                            Some(text) => escaped.write_str(text)?,
                            // Unless macros were expanded inside it, then its (expanded)
                            // contents are written as plain-text.
                            None => PlainTextFormatter::generate_children(&mut escaped, rest)?,
                        }
                    },
                    "textarea" | "title" => { // Not raw source-code, but plain-text.
                        // We have to reconsititute what the source-code would look like if all
                        // macros were expanded by hand, and read as raw source code.
                        PlainTextFormatter::generate_children(&mut Escaping(f), rest)?;
                    },
                    "style" => {  // <style> tag needs to generate CSS.
                        // When just a string is passed, don't convert. Assume raw CSS.
                        if let Some(ParseNode::String(string_node) | ParseNode::Raw(string_node)) = rest.first() {
                            if rest.len() != 1 {
                                return Err(GenerationError {
                                    markup: "HTML+CSS",
                                    message: String::from("A `style' tag can either have S-expression CSS rules, or\
                                        a single string containing raw CSS be passed in.\n\
                                        A string was passed in, but excess expressions were passed \
                                        in after that!"),
                                    site: string_node.site
                                });
                            }
                            // Otherwise, write that raw CSS.
                            write!(f, "{}", string_node.value)?;
                        } else {
                            writeln!(f)?;
                            CSSFormatter::generate_children(f, rest)?;
                        }
                    },
                    "script" => {
                        // When just a string is passed, it is the script, written as is.
                        if let [ParseNode::String(script) | ParseNode::Raw(script)] = rest {
                            write!(f, "{}", script.value)?;
                        } else if !rest.is_empty() {
                            // Otherwise, s-expressions are written in the language of the
                            // script's `type`: JavaScript, JSON, or else kept as written.
                            let tree: ParseTree<'a> = rest.to_vec().into_boxed_slice();
                            let formatter: Option<Box<dyn MarkupFormatter<'a>>> = match script_language(list)? {
                                ScriptLanguage::JavaScript => Some(Box::new(JSFormatter::new(tree))),
                                ScriptLanguage::Json => Some(Box::new(json::JSONFormatter::new(tree))),
                                ScriptLanguage::Other => None,
                            };
                            match formatter {
                                // Written over several lines when the source is, else on one line.
                                Some(formatter) if is_first_node_on_next_line =>
                                    write!(f, "\n{}", formatter.document()?.trim_end())?,
                                Some(formatter) => formatter.generate(f)?,
                                None => for (index, node) in rest.iter().enumerate() {
                                    generate_script(f, node, child_whitespace(index, node))?;
                                },
                            }
                        }
                    },
                    "math" | "svg" => {  // <math> and <svg> are subsets of XML.
                        XMLFormatter::generate_children(f, rest)?;
                    },
                    _ => {  // Tag contains regular old HTML.
                        Self::generate_children(f, rest)?;
                    },
                }
                // Closing tag should be equally as spaced as opening tag (?)
                if end_token.leading_whitespace.is_empty() {
                    if is_first_node_on_next_line || tag == "style" {
                        write!(f, "{leading}")?;
                    }
                } else {
                    write!(f, "{}", end_token.leading_whitespace)?;
                }

                write!(f, "</{tag}>")?;
            },
            ParseNode::Attribute { site, .. } =>
                return Err(GenerationError::new("HTML",
                    "Unexpected attribute encountered.", site))
        }
        Ok(())
    }
}

pub const DEFAULT: &str =
    "<!DOCTYPE html>\n\
    <html>\n\
        <head></head>\n\
        <body>\n\
            <!-- Generated by SEAM (empty file) -->\n\
        </body>\n\
    </html>\n";

/// Elements which belong in the `<head>` when they appear before any of the
/// document's content (as in the HTML parsing algorithm's "in head" mode).
const METADATA_ELEMENTS: [&str; 8] = [
    "base",
    "link",
    "meta",
    "noscript",
    "script",
    "style",
    "template",
    "title",
];

/// The language that a script's contents are written in, from its `type`.
enum ScriptLanguage { JavaScript, Json, Other }

fn script_language<'a>(element: &[ParseNode<'a>]) -> Result<ScriptLanguage, GenerationError<'a>> {
    let mut kind = None;
    for node in element.iter().skip(1) {
        let ParseNode::Attribute { keyword, node, .. } = node else { break };
        if keyword.eq_ignore_ascii_case("type") {
            kind = Some(attribute_value(node)?.trim().to_ascii_lowercase());
        }
    }
    Ok(match kind.as_deref() {
        None | Some("" | "module" | "text/javascript" | "application/javascript"
            | "text/ecmascript" | "application/ecmascript") => ScriptLanguage::JavaScript,
        Some("importmap" | "speculationrules" | "application/json" | "text/json") => ScriptLanguage::Json,
        Some(kind) if kind.ends_with("+json") => ScriptLanguage::Json,
        Some(_) => ScriptLanguage::Other,
    })
}

/// Write the source of a script as it was written, except that strings are
/// JavaScript string literals, and raw text (e.g. JSON) is written as is.
fn generate_script<'a>(f: Formatter, node: &ParseNode<'a>, leading: &str) -> Result<(), GenerationError<'a>> {
    write!(f, "{leading}")?;
    match node {
        ParseNode::Symbol(atom) | ParseNode::Number(atom) | ParseNode::Raw(atom) => write!(f, "{}", atom.value)?,
        ParseNode::String(string) => json::write_string(f, &string.value)?,
        ParseNode::List { nodes, end_token, .. } => {
            write!(f, "(")?;
            for node in nodes {
                generate_script(f, node, node.leading_whitespace())?;
            }
            write!(f, "{})", end_token.leading_whitespace)?;
        },
        ParseNode::Attribute { keyword, node, .. } => {
            write!(f, ":{keyword}")?;
            generate_script(f, node, node.leading_whitespace())?;
        },
    }
    Ok(())
}

fn tag_name(node: &ParseNode) -> Option<String> {
    match node {
        ParseNode::List { nodes, .. } => nodes.first()
            .and_then(ParseNode::symbol)
            .map(|symbol| symbol.value.to_ascii_lowercase()),
        _ => None,
    }
}

/// Text consisting only of whitespace, which may appear between elements.
fn is_blank(node: &ParseNode) -> bool {
    matches!(node, ParseNode::String(text) | ParseNode::Raw(text) if text.value.trim().is_empty())
}

/// A node of the completed HTML document, borrowing from the expanded tree.
enum Part<'t, 'a> {
    /// The `<!DOCTYPE html>` declaration, when none was written.
    Doctype,
    /// A node as it was written, which may be made to start on a new line.
    Written { node: &'t ParseNode<'a>, new_line: bool },
    /// An `html`, `head` or `body` element which was not written, or which
    /// was written, but has had loose nodes moved into it.
    Element {
        tag: &'t str,
        attributes: &'t [ParseNode<'a>],
        children: Vec<Part<'t, 'a>>,
        leading: &'t str,
        closing: &'t str,
    },
}

/// Whitespace starting on a new line: as given if it does, or else a new line.
fn on_new_line(whitespace: &str) -> &str {
    if whitespace.contains('\n') { whitespace } else { "\n" }
}

/// Split an element into its tag, attributes, children and closing whitespace.
fn element_parts<'t, 'a>(node: &'t ParseNode<'a>) -> (&'t str, &'t [ParseNode<'a>], &'t [ParseNode<'a>], &'t str) {
    let ParseNode::List { nodes, end_token, .. } = node else {
        unreachable!("only elements are split");
    };
    let tag = nodes.first().and_then(ParseNode::symbol).map_or("", |tag| &*tag.value);
    let attributes = nodes.iter().skip(1).take_while(|node| node.is_attribute()).count();
    let (attributes, children) = nodes[1..].split_at(attributes);
    (tag, attributes, children, end_token.leading_whitespace)
}

/// An element which was written, with loose nodes moved into it
/// (after its attributes, and at the end), or as written if there are none.
fn extend_element<'t, 'a>(node: &'t ParseNode<'a>, before: Vec<&'t ParseNode<'a>>, after: Vec<&'t ParseNode<'a>>) -> Part<'t, 'a> {
    if before.is_empty() && after.is_empty() {
        return Part::Written { node, new_line: true };
    }
    let (tag, attributes, children, closing) = element_parts(node);
    let written = |node| Part::Written { node, new_line: false };
    Part::Element {
        tag,
        attributes,
        children: before.into_iter().chain(children).chain(after).map(written).collect(),
        leading: on_new_line(node.leading_whitespace()),
        // Children were moved in, so close the element on its own line.
        closing: if closing.is_empty() { "\n" } else { closing },
    }
}

/// An element which was not written, containing loose nodes,
/// the first of which starts on a new line.
fn added_element<'t, 'a>(tag: &'static str, children: Vec<&'t ParseNode<'a>>, closing: &'static str) -> Part<'t, 'a> {
    let children = children.into_iter().enumerate()
        .map(|(index, node)| Part::Written { node, new_line: index == 0 })
        .collect();
    Part::Element { tag, attributes: &[], children, leading: "\n", closing }
}

/// Plan a complete HTML document, of the form
/// `(!DOCTYPE html) (html (head ...) (body ...))`, adding whichever of
/// those elements were not written explicitly.
/// Only the top-level and the inside of `(html ...)` are examined.
/// Loose metadata (e.g. `title`, `meta`, `style`) goes into the `<head>` until
/// the first piece of content, after which everything goes into the `<body>`,
/// as browsers do when parsing HTML with omitted tags.
fn plan_document<'t, 'a>(tree: &'t [ParseNode<'a>]) -> Result<Vec<Part<'t, 'a>>, GenerationError<'a>> {
    let mut nodes = tree.iter().peekable();
    let mut document = Vec::with_capacity(2);
    // Keep any doctype given, else provide one.
    let doctype = nodes.next_if(|node| tag_name(node).as_deref() == Some("!doctype"));
    document.push(doctype.map_or(Part::Doctype, |node| Part::Written { node, new_line: false }));
    let rest: Vec<&'t ParseNode<'a>> = nodes.collect();

    // Find the `(html ...)` element, if given, it must contain everything.
    let html_index = rest.iter().position(|node| tag_name(node).as_deref() == Some("html"));
    // The `html` element starts on a new line, unless it directly follows a written doctype.
    let html_on_new_line = doctype.is_none() || html_index != Some(0);
    let (html, contents): (Option<&'t ParseNode<'a>>, Vec<&'t ParseNode<'a>>) = if let Some(index) = html_index {
        if let Some(stray) = rest.iter().enumerate().find(|&(i, node)| i != index && !is_blank(node)) {
            return Err(GenerationError::new("HTML",
                "Content is not allowed outside of the `html' element.",
                stray.1.site()));
        }
        let (_, _, children, _) = element_parts(rest[index]);
        (Some(rest[index]), children.iter().collect())
    } else {
        (None, rest)
    };

    // Sort out the contents of the `(html ...)` element.
    let mut head: Option<&'t ParseNode<'a>> = None;
    let mut body: Option<&'t ParseNode<'a>> = None;
    let (mut before_head, mut after_head) = (vec![], vec![]);
    let (mut before_body, mut after_body) = (vec![], vec![]);
    let mut in_body = false;  // Switches on at the first piece of content.
    for node in contents {
        match tag_name(node).as_deref() {
            Some("head") => {
                if head.is_some() {
                    return Err(GenerationError::new("HTML",
                        "A document can only have one `head' element.", node.site()));
                }
                if in_body {
                    return Err(GenerationError::new("HTML",
                        "The `head' element must come before any of the document's content.",
                        node.site()));
                }
                head = Some(node);
            },
            Some("body") => {
                if body.is_some() {
                    return Err(GenerationError::new("HTML",
                        "A document can only have one `body' element.", node.site()));
                }
                in_body = true;
                body = Some(node);
            },
            Some(tag @ ("html" | "!doctype")) => {
                return Err(GenerationError::new("HTML",
                    &format!("Unexpected `{tag}' inside of the `html' element."),
                    node.site()));
            },
            Some(tag) if !in_body && METADATA_ELEMENTS.contains(&tag) => {
                if head.is_some() { after_head.push(node) } else { before_head.push(node) }
            },
            _ if !in_body && is_blank(node) => {},
            _ => {
                in_body = true;
                if body.is_some() { after_body.push(node) } else { before_body.push(node) }
            },
        }
    }

    let unchanged = head.is_some() && body.is_some()
        && before_head.is_empty() && after_head.is_empty()
        && before_body.is_empty() && after_body.is_empty();
    if let (Some(html), true) = (html, unchanged) {
        document.push(Part::Written { node: html, new_line: html_on_new_line });
        return Ok(document);
    }

    let head = match head {
        Some(head) => extend_element(head, before_head, after_head),
        None => added_element("head", before_head, ""),
    };
    let body = match body {
        Some(body) => extend_element(body, before_body, after_body),
        None => added_element("body", before_body, "\n"),
    };
    document.push(if let Some(html) = html {
        let (tag, attributes, _, closing) = element_parts(html);
        let leading = html.leading_whitespace();
        Part::Element {
            tag,
            attributes,
            children: vec![head, body],
            leading: if html_on_new_line { on_new_line(leading) } else { leading },
            closing: if closing.is_empty() { "\n" } else { closing },
        }
    } else {
        Part::Element { tag: "html", attributes: &[], children: vec![head, body], leading: "\n", closing: "\n" }
    });
    Ok(document)
}

impl<'a> HTMLFormatter<'a> {
    /// Write a planned part of the document, preceded by `leading` whitespace
    /// (if given, otherwise the part's own).
    fn generate_part(f: Formatter, part: &Part<'_, 'a>, leading: Option<&str>) -> Result<(), GenerationError<'a>> {
        match part {
            Part::Doctype => write!(f, "<!DOCTYPE html>")?,
            Part::Written { node, new_line } => {
                let whitespace = node.leading_whitespace();
                let whitespace = if *new_line { on_new_line(whitespace) } else { leading.unwrap_or(whitespace) };
                Self::generate_html_node(f, node, whitespace)?;
            },
            Part::Element { tag, attributes, children, leading, closing } => {
                write!(f, "{leading}<{tag}")?;
                Self::generate_attributes(f, attributes)?;
                write!(f, ">")?;
                let mut first_on_new_line = false;
                for (index, child) in children.iter().enumerate() {
                    let whitespace = match child {
                        Part::Written { node, new_line: false } => Some(child_whitespace(index, node)),
                        _ => None,
                    };
                    if index == 0 {
                        first_on_new_line = match child {
                            Part::Written { node, new_line } => *new_line || node.leading_whitespace().contains('\n'),
                            Part::Element { leading, .. } => leading.contains('\n'),
                            Part::Doctype => false,
                        };
                    }
                    Self::generate_part(f, child, whitespace)?;
                }
                // Closing tag is spaced as the opening tag, when the contents start on a new line.
                if closing.is_empty() {
                    if first_on_new_line {
                        write!(f, "{leading}")?;
                    }
                } else {
                    write!(f, "{closing}")?;
                }
                write!(f, "</{}>", tag.to_ascii_lowercase())?;
            },
        }
        Ok(())
    }
}

/// HTML void elements do not get a closing `</...>` tag. They are self-closing.
const VOID_ELEMENTS: [&str; 14] = [
    "area",
    "base",
    "br",
    "col",
    "embed",
    "hr",
    "img",
    "input",
    "link",
    "meta",
    "param",
    "source",
    "track",
    "wbr",
];

impl<'a> MarkupFormatter<'a> for HTMLFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError<'a>> {
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }
        let mut document = String::new();
        for part in &plan_document(&self.tree)? {
            Self::generate_part(&mut document, part, None)?;
        }
        Ok(document)
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError<'a>> {
        Self::generate_nodes(f, &self.tree)
    }
}

/// Whether some source text is only whitespace and comments.
fn is_blank_source(text: &str) -> bool {
    let mut in_comment = false;
    text.chars().all(|c| {
        match c {
            ';' => in_comment = true,
            '\n' => in_comment = false,
            _ => {},
        }
        in_comment || c.is_whitespace()
    })
}

/// Check that `nodes` are exactly as written in `file`, in order from `cursor`,
/// with only whitespace and comments between them, advancing `cursor` past them.
/// Nodes produced by expanding macros or variables do not sit like this.
fn as_written(nodes: &[ParseNode], file: &tokens::SourceFile, cursor: &mut usize) -> bool {
    let code: &str = &file.code;
    nodes.iter().all(|node| {
        let site = node.site();
        if !std::ptr::eq(site.file, file) || site.start() < *cursor
            || !code.get(*cursor..site.start()).is_some_and(is_blank_source) {
            return false;
        }
        *cursor = site.end();
        match node {
            ParseNode::List { nodes, end_token, .. } => {
                let inner = as_written(nodes, file, cursor)
                    && code.get(*cursor..end_token.site.start()).is_some_and(is_blank_source);
                *cursor = end_token.site.end();
                inner
            },
            ParseNode::Attribute { node, .. } => as_written(std::slice::from_ref(node), file, cursor),
            _ => true,
        }
    })
}

/// The text inside an element, `(tag ...)`, exactly as written in the source
/// (after its tag and any attributes, less a single separating space),
/// as long as its contents were not changed by expanding any macros.
fn verbatim_text<'a>(list: &[ParseNode<'a>], end_token: &tokens::Token<'a>) -> Option<&'a str> {
    let file = end_token.site.file;
    let attributes = list.iter().skip(1).take_while(|node| node.is_attribute()).count();
    let (head, contents) = list.split_at(1 + attributes);
    // The tag and attributes must be as written too, the text starts after them.
    let mut cursor = head.first()?.site().start();
    if !as_written(head, file, &mut cursor) {
        return None;
    }
    let start = cursor;
    if !as_written(contents, file, &mut cursor) {
        return None;
    }
    let code = end_token.site.source_code();
    let end = end_token.site.start();
    if !code.get(cursor..end).is_some_and(is_blank_source) {
        return None;
    }
    let text = code.get(start..end)?;
    Some(text.strip_prefix(' ').unwrap_or(text))
}

/// The text of an attribute's value: an atom as it is, a list of
/// properties as CSS declarations (e.g. `:style (:color red :margin 0)`),
/// or a list of atoms separated by spaces (e.g. `:class (post wide)`).
fn attribute_value<'a, 'n>(node: &'n ParseNode<'a>) -> Result<Cow<'n, str>, GenerationError<'a>> {
    if let Some(atom) = node.atomic() {
        return Ok(Cow::Borrowed(&atom.value));
    }
    let non_atomic = |site| GenerationError::new("HTML",
        "Attribute values are atoms, lists of atoms, or lists of `:property value` pairs.", site);
    let Some(items) = node.list() else { return Err(non_atomic(node.site())) };
    let mut text = String::new();
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            text.push(' ');
        }
        match item {
            ParseNode::Attribute { keyword, node: value, .. } => {
                text += keyword;
                text += ": ";
                text += &css::css_value(keyword, value)?;
                text.push(';');
            },
            _ => text += &item.atomic().ok_or_else(|| non_atomic(item.site()))?.value,
        }
    }
    Ok(Cow::Owned(text))
}
