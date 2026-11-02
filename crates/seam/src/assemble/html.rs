//! Assembles an expanded tree into valid HTML.

use super::{escape_xml, GenerationError, MarkupFormatter, Formatter};
use super::{
    text::PlainTextFormatter,
    sexp::SExpFormatter,
    xml::XMLFormatter,
    css::CSSFormatter,
};

use crate::parse::parser::{Node, ParseNode, ParseTree};
use crate::parse::tokens::{self, Kind, Site, Token};

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

    fn generate_html_node(f: Formatter, node: &ParseNode<'a>) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
            | ParseNode::Number(node)
            | ParseNode::String(node) => {
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", escape_xml(&node.value))?;
            },
            ParseNode::Raw(node) => {
                // Don't escape any symbols in a raw-content string.
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", node.value)?;
            },
            ParseNode::List { nodes: list, leading_whitespace, end_token, .. } => {
                write!(f, "{leading_whitespace}")?;
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

                while let Some(ParseNode::Attribute { node, keyword, leading_whitespace, .. }) = rest.first() {
                    if let Some(atom) = (*node).atomic() {
                        let leading_whitespace
                            = if leading_whitespace.is_empty()
                              { " " } else { leading_whitespace };
                        write!(f, "{leading_whitespace}")?;
                        write!(f, "{}=\"{}\"", keyword, atom.value)?;
                        rest = &rest[1..];
                    } else {
                        // Error! Cannot be non atomic.
                        return Err(GenerationError::new("HTML",
                            "Attribute cannot contain non-atomic data.",
                            (*node).site()));
                    }
                }
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
                let rest_with_preserved_whitespace = rest;
                let mut rest: Vec<ParseNode<'a>> = rest_with_preserved_whitespace.to_vec();
                let mut is_first_node_on_next_line = false;
                if let Some(first_node) = rest.get_mut(0) {
                    is_first_node_on_next_line = first_node.leading_whitespace().contains('\n');
                    if !is_first_node_on_next_line {
                        first_node.set_leading_whitespace(String::new());
                    }
                }

                // Handle tags which *do not* contain HTML as syntax:
                //    <pre>, <style>, <script>, <math>, <svg>, <textarea>, <title>
                // Specifically:
                //   - <svg> and <math> contain XML, not HTML;
                //   - <pre>, <textarea> and <title> contain raw text, not parsed as HTML;
                //   - <pre> will display raw text found in source code;
                //   - <textarea> and <title> however, are escapable (evaluate macros);
                //   - <script> contains JavaScript, maybe we will parse this in the future!;
                //   - <style> contains CSS, which we have our own parser for already.
                match tag.as_str() {
                    "pre" => { // <pre> should preserve the raw text in the *source* file.
                        // Find beginning and end byte offset of first and last token inside
                        // of `(pre ...)` and simply clone the text between those offsets.
                        let pre = raw_text(rest_with_preserved_whitespace.first(), end_token);
                        write!(f, "{pre}")?;
                    },
                    "textarea" | "title" => { // Not eaw source-code, but plain-text.
                        // We have to reconsititute what the source-code would look like if all
                        // macros were expanded by hand, and read as raw source code.
                        let text_fmt = PlainTextFormatter::new(rest.into_boxed_slice());
                        text_fmt.generate(f)?;
                    },
                    "style" => {  // <style> tag needs to generate CSS.
                        // When just a string is passed, don't convert. Assume raw CSS.
                        if let Some(ParseNode::String(string_node)) = rest.first() {
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
                            let css_fmt = CSSFormatter::new(rest.into_boxed_slice());
                            css_fmt.generate(f)?;
                        }
                    },
                    "script" => {
                        // TODO: Generating JavaScript from S-expressions is not implemented.
                        // For now, just treat it as a completely source-code preserving.
                        let sexp_fmt = SExpFormatter::new(rest.into_boxed_slice());
                        sexp_fmt.generate(f)?;
                    },
                    "math" | "svg" => {  // <math> and <svg> are subsets of XML.
                        let xml_fmt = XMLFormatter::new(rest.into_boxed_slice());
                        xml_fmt.generate(f)?;
                    },
                    _ => {  // Tag contains regular old HTML.
                        let html_fmt = HTMLFormatter::new(rest.into_boxed_slice());
                        html_fmt.generate(f)?;
                    },
                }
                // Closing tag should be equally as spaced as opening tag (?)
                if end_token.leading_whitespace.is_empty() {
                    if is_first_node_on_next_line || tag == "style" {
                        write!(f, "{leading_whitespace}")?;
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

/// Lower-cased tag name of an element node, e.g. `(Body ...)` gives `body`.
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

/// Build an element `(tag ...children)` which was not written in the source.
fn element<'a>(tag: &str, children: Vec<ParseNode<'a>>, site: Site<'a>,
               leading_whitespace: &str, closing_whitespace: &'static str) -> ParseNode<'a> {
    let mut nodes = Vec::with_capacity(children.len() + 1);
    nodes.push(ParseNode::Symbol(Node::new(tag, &site, "")));
    nodes.extend(children);
    ParseNode::List {
        nodes: nodes.into_boxed_slice(),
        site,
        end_token: Token::new(Kind::RParen, ")", closing_whitespace, site),
        leading_whitespace: leading_whitespace.to_owned(),
    }
}

/// Insert extra children into an existing element, after any attributes,
/// and at the end, leaving the element untouched if there is nothing to add.
fn extend_element<'a>(node: ParseNode<'a>, before: Vec<ParseNode<'a>>, after: Vec<ParseNode<'a>>) -> ParseNode<'a> {
    if before.is_empty() && after.is_empty() {
        return node;
    }
    let ParseNode::List { nodes, site, mut end_token, leading_whitespace } = node else {
        unreachable!("only elements are extended");
    };
    let attributes = nodes.iter().skip(1).take_while(|node| node.is_attribute()).count();
    let (head, children) = nodes.split_at(attributes + 1);
    let mut nodes = head.to_vec();
    nodes.extend(before);
    nodes.extend_from_slice(children);
    nodes.extend(after);
    // Children were moved in, so close the element on its own line.
    if end_token.leading_whitespace.is_empty() {
        end_token.leading_whitespace = "\n";
    }
    ParseNode::List { nodes: nodes.into_boxed_slice(), site, end_token, leading_whitespace }
}

/// Make sure the first child of a generated element starts on a new line.
fn on_new_line(nodes: &mut [ParseNode]) {
    if let Some(first) = nodes.first_mut()
        && !first.leading_whitespace().contains('\n') {
        first.set_leading_whitespace(String::from("\n"));
    }
}

/// Rearrange a tree into a complete HTML document, of the form
/// `(!DOCTYPE html) (html (head ...) (body ...))`, adding whichever of
/// those elements were not written explicitly.
/// Only the top-level and the inside of `(html ...)` are examined.
/// Loose metadata (e.g. `title`, `meta`, `style`) goes into the `<head>` until
/// the first piece of content, after which everything goes into the `<body>`,
/// as browsers do when parsing HTML with omitted tags.
fn normalize_document<'a>(tree: &[ParseNode<'a>]) -> Result<ParseTree<'a>, GenerationError<'a>> {
    let mut nodes = tree.iter().peekable();
    let mut document = Vec::with_capacity(2);
    // Keep any doctype given, else provide one.
    let doctype = nodes.next_if(|node| tag_name(node).as_deref() == Some("!doctype"));
    let site = doctype.or_else(|| tree.first()).map_or_else(Site::unknown, ParseNode::owned_site);
    document.push(doctype.cloned().unwrap_or_else(|| element("!DOCTYPE",
        vec![ParseNode::Symbol(Node::new("html", &site, " "))], site, "", "")));
    let rest: Vec<&ParseNode<'a>> = nodes.collect();

    // Find the `(html ...)` element, if given, it must contain everything.
    let html = rest.iter().position(|node| tag_name(node).as_deref() == Some("html"));
    let html = if let Some(index) = html {
        if let Some(stray) = rest.iter().enumerate().find(|&(i, node)| i != index && !is_blank(node)) {
            return Err(GenerationError::new("HTML",
                "Content is not allowed outside of the `html' element.",
                stray.1.site()));
        }
        let mut html = rest[index].clone();
        if doctype.is_none_or(|_| index != 0) && !html.leading_whitespace().contains('\n') {
            html.set_leading_whitespace(String::from("\n"));
        }
        html
    } else {
        element("html", rest.into_iter().cloned().collect(), site, "\n", "\n")
    };

    // Sort out the contents of the `(html ...)` element.
    let ParseNode::List { nodes, site, end_token, leading_whitespace } = html else { unreachable!() };
    let attributes = nodes.iter().skip(1).take_while(|node| node.is_attribute()).count();
    let (html_head, contents) = nodes.split_at(attributes + 1);

    let mut head: Option<ParseNode<'a>> = None;
    let mut body: Option<ParseNode<'a>> = None;
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
                head = Some(node.clone());
            },
            Some("body") => {
                if body.is_some() {
                    return Err(GenerationError::new("HTML",
                        "A document can only have one `body' element.", node.site()));
                }
                in_body = true;
                body = Some(node.clone());
            },
            Some(tag @ ("html" | "!doctype")) => {
                return Err(GenerationError::new("HTML",
                    &format!("Unexpected `{tag}' inside of the `html' element."),
                    node.site()));
            },
            Some(tag) if !in_body && METADATA_ELEMENTS.contains(&tag) => {
                if head.is_some() { after_head.push(node.clone()) } else { before_head.push(node.clone()) }
            },
            _ if !in_body && is_blank(node) => {},
            _ => {
                in_body = true;
                if body.is_some() { after_body.push(node.clone()) } else { before_body.push(node.clone()) }
            },
        }
    }

    let unchanged = head.is_some() && body.is_some()
        && before_head.is_empty() && after_head.is_empty()
        && before_body.is_empty() && after_body.is_empty();
    if unchanged {
        document.push(ParseNode::List { nodes, site, end_token, leading_whitespace });
        return Ok(document.into_boxed_slice());
    }

    let head = if let Some(head) = head {
        extend_element(head, before_head, after_head)
    } else {
        on_new_line(&mut before_head);
        element("head", before_head, site, "\n", "")
    };
    let body = if let Some(body) = body {
        extend_element(body, before_body, after_body)
    } else {
        on_new_line(&mut before_body);
        element("body", before_body, site, "\n", "\n")
    };
    let mut html_nodes = html_head.to_vec();
    let start = html_nodes.len();
    html_nodes.push(head);
    html_nodes.push(body);
    on_new_line(&mut html_nodes[start..=start]);
    on_new_line(&mut html_nodes[start + 1..]);
    let mut end_token = end_token;
    if end_token.leading_whitespace.is_empty() {
        end_token.leading_whitespace = "\n";
    }
    document.push(ParseNode::List { nodes: html_nodes.into_boxed_slice(), site, end_token, leading_whitespace });
    Ok(document.into_boxed_slice())
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
        let document = HTMLFormatter::new(normalize_document(&self.tree)?);
        document.display()
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError<'a>> {
        let tree_iter = self.tree.iter().peekable();
        for node in tree_iter {
            Self::generate_html_node(f, node)?;
        }
        Ok(())
    }
}

/// Get raw text in source-file between a `start_node` and some `end_token`.
/// Does not work well if the `start_node` is a result of a macro expansion,
/// it must be a plain node.
/// Especially, the first node cannot be the result of an `(%include)` macro,
/// i.e. from a different file (we explicitly crash in this case).
/// This is a limitation from the fact that we do not know what kind of markup
/// format we are targetting until *after* parsing and expanding.
fn raw_text<'a>(start_node: Option<&ParseNode<'a>>, end_token: &tokens::Token<'a>) -> &'a str {
    let Some(start_node) = start_node else {
        return end_token.leading_whitespace;
    };
    assert!(std::ptr::eq(start_node.site().source_code, end_token.site.source_code), "Start of preformatted text tag must belong to the same source location.");
    let source: &'a str = end_token.site.source_code;
    let first_node_offset =
          start_node.site().bytes_from_start
        - start_node.leading_whitespace().len()
        + usize::from(start_node.leading_whitespace().starts_with(' '));
    &source[first_node_offset..end_token.site.bytes_from_start]
}
