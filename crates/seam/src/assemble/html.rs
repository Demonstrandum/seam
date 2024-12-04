//! Assembles an expanded tree into valid HTML.
use std::cell::RefCell;

use super::{escape_xml, GenerationError, MarkupFormatter, Formatter};
use super::{
    text::PlainTextFormatter,
    sexp::SExpFormatter,
    xml::XMLFormatter,
    css::CSSFormatter,
};

use crate::parse::parser::{ParseNode, ParseTree, SearchTree, SearchType};
use crate::parse::tokens;

#[derive(Debug, Clone)]
pub struct HTMLFormatter<'a> {
    pub tree: ParseTree<'a>,
    formatters: RefCell<Vec<Box<dyn MarkupFormatter + 'a>>>,
}

impl<'a> HTMLFormatter<'a> {
    pub fn new(tree: ParseTree<'a>) -> Self {
        Self {
            tree,
            formatters: Default::default(),
        }
    }

    fn register_formatter<Fmt: MarkupFormatter + 'a>(&self, formatter: Fmt) -> &'a Box<dyn MarkupFormatter + 'a> {
        let fmts = self.formatters.as_ptr();
        unsafe {
            (*fmts).push(Box::new(formatter));
            (*fmts).last().unwrap()
        }
    }

    fn generate_html_node(&self, f: Formatter, node: &ParseNode<'a>) -> Result<(), GenerationError<'a>> {
        match node {
            ParseNode::Symbol(node)
            | ParseNode::Number(node) => {
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", escape_xml(&node.value))?;
            },
            ParseNode::String(node) => {
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", escape_xml(&node.value))?;
            },
            ParseNode::Raw(node) => {
                // Don't escape any symbols in a raw-content string.
                write!(f, "{}", node.leading_whitespace)?;
                write!(f, "{}", &node.value)?;
            },
            ParseNode::List { nodes: list, leading_whitespace, end_token, .. } => {
                write!(f, "{}", leading_whitespace)?;
                let head = list.first();
                let tag: &str;  // html <tag> name.
                if let Some(head_node) = head {
                    if let ParseNode::Symbol(head_symbol) = head_node {
                        tag = &head_symbol.value;
                        write!(f, "<{}", tag)?;
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
                if tag.as_bytes()[0] == '!' as u8 {
                    while !rest.is_empty() {
                        if let Some(node) = rest[0].symbolic() {
                            write!(f, " {}", node.value)?;
                        } else {
                            return Err(GenerationError::new("HTML",
                                "Non-symbolic item in declaration",
                                &rest[0].site()));
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
                        write!(f, "{}", leading_whitespace)?;
                        write!(f, "{}=\"{}\"", keyword, atom.value)?;
                        rest = &rest[1..];
                    } else {
                        // Error! Cannot be non atomic.
                        return Err(GenerationError::new("HTML",
                            "Attribute cannot contain non-atomic data.",
                            &(*node).site()));
                    }
                }
                write!(f, ">")?;

                // Check early if this tag is a void element.
                if VOID_ELEMENTS.binary_search(&tag.as_str()).is_ok() {
                    // Void elements cannot have children.
                    if let Some(child_node) = rest.first() {
                        return Err(GenerationError::new("HTML",
                            &format!("A void element such as `<{}>' cannot have children.", tag),
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
                        first_node.set_leading_whitespace("".to_owned());
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
                        write!(f, "{}", pre)?;
                    },
                    "textarea" | "title" => { // Not eaw source-code, but plain-text.
                        // We have to reconsititute what the source-code would look like if all
                        // macros were expanded by hand, and read as raw source code.
                        let text_fmt = PlainTextFormatter::new(rest.into_boxed_slice());
                        let text_fmt = self.register_formatter(text_fmt);
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
                                    site: string_node.site.clone()
                                });
                            }
                            // Otherwise, write that raw CSS.
                            write!(f, "{}", string_node.value)?;
                        } else {
                        writeln!(f, "")?;
                            let css_fmt = CSSFormatter::new(rest.into_boxed_slice());
                            let css_fmt = self.register_formatter(css_fmt);
                            css_fmt.generate(f)?;
                        }
                    },
                    "script" => {
                        // TODO: Generating JavaScript from S-expressions is not implemented.
                        // For now, just treat it as a completely source-code preserving.
                        let sexp_fmt = SExpFormatter::new(rest.into_boxed_slice());
                        let sexp_fmt = self.register_formatter(sexp_fmt);
                        sexp_fmt.generate(f)?;
                    },
                    "math" | "svg" => {  // <math> and <svg> are subsets of XML.
                        let xml_fmt = XMLFormatter::new(rest.into_boxed_slice());
                        let xml_fmt = self.register_formatter(xml_fmt);
                        xml_fmt.generate(f)?;
                    },
                    _ => {  // Tag contains regular old HTML.
                        let html_fmt = HTMLFormatter::new(rest.into_boxed_slice());
                        let html_fmt = self.register_formatter(html_fmt);
                        html_fmt.generate(f)?;
                    },
                }
                // Closing tag should be equally as spaced as opening tag (?)
                if end_token.leading_whitespace.is_empty() {
                    if is_first_node_on_next_line || tag == "style" {
                        write!(f, "{}", leading_whitespace)?;
                    }
                } else {
                    write!(f, "{}", end_token.leading_whitespace)?;
                }

                write!(f, "</{}>", tag)?;
            },
            ParseNode::Attribute { ref site, .. } =>
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

impl<'a> MarkupFormatter for HTMLFormatter<'a> {
    fn document(&self) -> Result<String, GenerationError> {
        let mut doc = String::new();
        if self.tree.is_empty() {
            return Ok(String::from(DEFAULT));
        }

        // Check if top-level <!DOCTYPE html> exists.
        let doctype_tag
            = self.tree.search_node(SearchType::ListHead, "!doctype", true, 1);
        // Check if top-level <html></html> root object exists.
        let html_tag
            = self.tree.search_node(SearchType::ListHead, "html", true, 1);
        // Check if <head></head> tag object exists.
        let head_tag
            = self.tree.search_node(SearchType::ListHead, "head", true, 2);
        // Check if <body></body> tag object exists.
        let body_tag
            = self.tree.search_node(SearchType::ListHead, "body", true, 2);

        if doctype_tag.is_none() {
            #[cfg(feature="debug")]
            eprintln!("html: no doctype found in document");
            doc += "<!DOCTYPE html>\n";
            if html_tag.is_none() {
                doc += "<html>\n";
                if head_tag.is_none() {
                    doc += "<head></head>\n"
                }
                if body_tag.is_none() {
                    doc += "<body>\n"
                }
            }
        }
        // Populate.
        doc += &self.display()?;
        doc += "\n";

        if doctype_tag.is_none() {
            if html_tag.is_none() {
                if body_tag.is_none() {
                    doc += "</body>\n"
                }
                doc += "</html>\n"
            }
        }

        if doc.ends_with('\n') { let _ = doc.pop(); }
        Ok(doc)
    }

    fn generate(&self, f: Formatter) -> Result<(), GenerationError> {
        let mut tree_iter = self.tree.iter().peekable();
        while let Some(node) = tree_iter.next() {
            self.generate_html_node(f, node)?;
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
    if !std::ptr::eq(start_node.site().source_code, end_token.site.source_code) {
        panic!("Start of preformatted text tag must belong to the same source location.");
    }
    let source: &'a str = end_token.site.source_code;
    let first_node_offset =
          start_node.site().bytes_from_start
        - start_node.leading_whitespace().len()
        + if start_node.leading_whitespace().starts_with(' ') { 1 } else { 0 };
    &source[first_node_offset..end_token.site.bytes_from_start]
}
