//! Macros for working with text, regular expressions, dictionaries and
//! lists of data, and `%cond`.

use super::code::{error, list_of};
use super::{Expander, ExpansionError, Number, list_node, truthy, bool_node, number_node, without_leading, spaced, node_text};
use crate::parse::parser::{Node, ParseNode, ParseTree};

type Expansion<'a> = Result<ParseTree<'a>, ExpansionError<'a>>;

/// The text of an atom.
fn text_of<'n, 'a>(node: &'n ParseNode<'a>, call: &ParseNode<'a>, what: &str) -> Result<&'n str, ExpansionError<'a>> {
    match node.atomic() {
        Some(atom) => Ok(&atom.value),
        None => Err(error(format!("{what} must be text, but got a {}.", node.node_type()), call)),
    }
}

/// A new atom of the same kind as `like` (a symbol stays a symbol, raw text
/// stays raw, anything else is a string), in the place of the call.
fn text_like<'a>(like: &ParseNode<'a>, call: &ParseNode<'a>, value: String) -> ParseNode<'a> {
    let node = Node::new(value, call.site(), call.leading_whitespace().clone());
    match like {
        ParseNode::Symbol(_) => ParseNode::Symbol(node),
        ParseNode::Raw(_) => ParseNode::Raw(node),
        _ => ParseNode::String(node),
    }
}

/// A whole number argument.
fn integer<'a>(node: &ParseNode<'a>, call: &ParseNode<'a>, what: &str) -> Result<i64, ExpansionError<'a>> {
    match Number::of(node) {
        Some(Number::Int(int)) => Ok(int),
        _ => Err(error(format!("{what} must be a whole number."), call)),
    }
}

/// Resolve a slice bound, counting from the end if negative, clamped to `length`.
fn bound(index: i64, length: usize) -> usize {
    if index < 0 {
        length.saturating_sub(usize::try_from(index.unsigned_abs()).unwrap_or(usize::MAX))
    } else {
        usize::try_from(index).unwrap_or(usize::MAX).min(length)
    }
}

fn compile<'a>(pattern: &str, call: &ParseNode<'a>) -> Result<regex::Regex, ExpansionError<'a>> {
    regex::Regex::new(pattern).map_err(|err| error(format!("Invalid regular expression: {err}"), call))
}

fn string_node<'a>(call: &ParseNode<'a>, value: &str, leading: &str) -> ParseNode<'a> {
    ParseNode::String(Node::new(value.to_owned(), call.site(), leading.to_owned()))
}

/// Set `key` to `value` in a dictionary's items, in place if it is there.
fn set_key<'a>(items: &mut Vec<ParseNode<'a>>, key: &str, value: ParseNode<'a>, attribute: ParseNode<'a>) {
    let existing = items.iter_mut().find_map(|item| match item {
        ParseNode::Attribute { keyword, node, .. } if keyword == key => Some(node),
        _ => None,
    });
    match existing {
        Some(node) => **node = value,
        None => items.push(attribute),
    }
}

/// The text a string macro is given: its single argument.
fn text_argument<'p, 'a>(name: &str, node: &ParseNode<'a>, params: &'p [ParseNode<'a>]) -> Result<&'p ParseNode<'a>, ExpansionError<'a>> {
    match params {
        [text] if text.is_atomic() => Ok(text),
        _ => Err(error(format!("`%{name}` takes a single piece of text."), node)),
    }
}

impl<'a> Expander<'a> {
    /// `(%upper s)`, `(%lower s)`, `(%capitalize s)`, `(%trim s)` and `(%slugify s)`.
    pub(super) fn expand_text_macro(&self, name: &str, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let text = text_argument(name, node, &params)?;
        let value = text_of(text, node, "The text")?;
        let changed = match name {
            "upper" => value.to_uppercase(),
            "lower" => value.to_lowercase(),
            "capitalize" | "capitalise" => {
                let mut chars = value.chars();
                chars.next().map_or_else(String::new, |first| first.to_uppercase().chain(chars).collect())
            },
            "trim" => value.trim().to_owned(),
            "slugify" => {
                // Lower-case letters and digits, with a `-` for each run of anything else.
                let mut slug = String::new();
                for c in value.chars() {
                    if c.is_alphanumeric() {
                        slug.extend(c.to_lowercase());
                    } else if !slug.is_empty() && !slug.ends_with('-') {
                        slug.push('-');
                    }
                }
                slug.trim_end_matches('-').to_owned()
            },
            _ => unreachable!("not a text macro"),
        };
        Ok(Box::new([text_like(text, node, changed)]))
    }

    /// `(%replace from to text)` replaces every `from` in the text with `to`.
    pub(super) fn expand_replace_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [from, to, text] = &*params else {
            return Err(error("`%replace` takes the text to find, its replacement, and the text.", node));
        };
        let from = text_of(from, node, "The text to find")?;
        if from.is_empty() {
            return Err(error("`%replace` cannot find empty text.", node));
        }
        let replaced = text_of(text, node, "The text")?.replace(from, text_of(to, node, "The replacement")?);
        Ok(Box::new([text_like(text, node, replaced)]))
    }

    /// `(%starts-with prefix text)` and `(%ends-with suffix text)`.
    pub(super) fn expand_affix_macro(&self, name: &str, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [affix, text] = &*params else {
            return Err(error(format!("`%{name}` takes the text to look for, and the text."), node));
        };
        let affix = text_of(affix, node, "The text to look for")?;
        let text = text_of(text, node, "The text")?;
        let is = if name == "starts-with" { text.starts_with(affix) } else { text.ends_with(affix) };
        Ok(Box::new([bool_node(node, is)]))
    }

    /// `(%slice start text)` or `(%slice start end text)`: the characters of
    /// text, or items of a list, from `start` up to `end`, counting from the
    /// end when negative.
    pub(super) fn expand_slice_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let (start, end, value) = match &*params {
            [start, value] => (integer(start, node, "The start")?, None, value),
            [start, end, value] => (integer(start, node, "The start")?, Some(integer(end, node, "The end")?), value),
            _ => return Err(error("`%slice` takes a start, optionally an end, and text or a list.", node)),
        };
        let range = |length: usize| {
            let start = bound(start, length);
            start..end.map_or(length, |end| bound(end, length)).max(start)
        };
        if let ParseNode::List { .. } = value {
            let items = list_of(value, node, "The list")?;
            let range = range(items.len());
            let sliced = items.into_iter().skip(range.start).take(range.len()).collect();
            return Ok(Box::new([list_node(node, without_leading(sliced))]));
        }
        let text = text_of(value, node, "The text")?;
        let chars: Vec<char> = text.chars().collect();
        let range = range(chars.len());
        Ok(Box::new([text_like(value, node, chars[range].iter().collect())]))
    }

    /// The `%regex/...` macros: `matches`, `find`, `captures`, `replace` and `split`.
    pub(super) fn expand_regex_macro(&self, name: &str, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let usage = || error(match name {
            "replace" => "`%regex/replace` takes a pattern, its replacement, and the text.".to_owned(),
            _ => format!("`%regex/{name}` takes a pattern, and the text."),
        }, node);
        let (pattern, replacement, text) = match (&*params, name) {
            ([pattern, replacement, text], "replace") => (pattern, Some(replacement), text),
            ([pattern, text], "matches" | "find" | "captures" | "split") => (pattern, None, text),
            _ => return Err(usage()),
        };
        let regex = compile(text_of(pattern, node, "The pattern")?, node)?;
        let value = text_of(text, node, "The text")?;
        let result = match name {
            "matches" => bool_node(node, regex.is_match(value)),
            "find" => list_node(node, regex.find_iter(value)
                .enumerate()
                .map(|(index, found)| string_node(node, found.as_str(), if index == 0 { "" } else { " " }))
                .collect::<Vec<_>>()),
            "captures" => {
                // The whole match then each group, or nothing if there is no match.
                let Some(captures) = regex.captures(value) else { return Ok(Box::new([])) };
                list_node(node, captures.iter()
                    .enumerate()
                    .map(|(index, group)| string_node(node, group.map_or("", |group| group.as_str()), if index == 0 { "" } else { " " }))
                    .collect::<Vec<_>>())
            },
            "replace" => {
                let replacement = text_of(replacement.expect("given"), node, "The replacement")?;
                text_like(text, node, regex.replace_all(value, replacement).into_owned())
            },
            "split" => list_node(node, regex.split(value)
                .enumerate()
                .map(|(index, part)| string_node(node, part, if index == 0 { "" } else { " " }))
                .collect::<Vec<_>>()),
            _ => unreachable!("not a regex macro"),
        };
        Ok(Box::new([result]))
    }

    /// `(%set :k v ... dict)` sets keys, keeping their place if already there.
    pub(super) fn expand_set_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let Some((dict, changes)) = params.split_last() else {
            return Err(error("`%set` takes `:key value` pairs, and a dictionary.", node));
        };
        let mut items = list_of(dict, node, "The dictionary")?;
        for change in changes {
            let ParseNode::Attribute { keyword, node: value, .. } = change else {
                return Err(error(format!("`%set` takes `:key value` pairs, but got a {}.", change.node_type()), node));
            };
            let mut attribute = change.clone();
            attribute.set_leading_whitespace(if items.is_empty() { "" } else { " " });
            set_key(&mut items, keyword, (**value).clone(), attribute);
        }
        Ok(Box::new([list_node(node, items)]))
    }

    /// `(%remove key ... dict)` gives the dictionary without those keys.
    pub(super) fn expand_remove_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let Some((dict, keys)) = params.split_last() else {
            return Err(error("`%remove` takes keys, and a dictionary.", node));
        };
        let keys = keys.iter().map(|key| text_of(key, node, "A key")).collect::<Result<Vec<_>, _>>()?;
        let items = list_of(dict, node, "The dictionary")?.into_iter()
            .filter(|item| !matches!(item, ParseNode::Attribute { keyword, .. } if keys.contains(&keyword.as_ref())))
            .collect();
        Ok(Box::new([list_node(node, without_leading(items))]))
    }

    /// `(%merge a b ...)` gives the keys of every dictionary, with later
    /// values replacing earlier ones in their place.
    pub(super) fn expand_merge_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let mut items: Vec<ParseNode<'a>> = vec![];
        for dict in &*params {
            for item in list_of(dict, node, "Each dictionary")? {
                match &item {
                    ParseNode::Attribute { keyword, node: value, .. } => {
                        let mut attribute = item.clone();
                        attribute.set_leading_whitespace(if items.is_empty() { "" } else { " " });
                        set_key(&mut items, keyword, (**value).clone(), attribute);
                    },
                    _ => items.push(item),
                }
            }
        }
        Ok(Box::new([list_node(node, items)]))
    }

    /// `(%chunk n list)` splits a list into lists of `n` items (the last may be shorter).
    pub(super) fn expand_chunk_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [size, list] = &*params else {
            return Err(error("`%chunk` takes a size, and a list.", node));
        };
        let size = usize::try_from(integer(size, node, "The size")?).ok().filter(|size| *size > 0)
            .ok_or_else(|| error("The size of a chunk must be at least 1.", node))?;
        let items = list_of(list, node, "The list")?;
        let chunks = items.chunks(size)
            .map(|chunk| list_node(node, without_leading(chunk.to_vec())))
            .collect();
        Ok(Box::new([list_node(node, spaced(chunks))]))
    }

    /// `(%sum list)` adds up a list of numbers, `0` if empty.
    pub(super) fn expand_sum_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [list] = &*params else {
            return Err(error("`%sum` takes a list of numbers.", node));
        };
        let items = list_of(list, node, "The list")?;
        if items.is_empty() {
            return Ok(Box::new([number_node(node, "0".to_owned())]));
        }
        let mut sum = self.expand_invocation("+", node, &items)?;
        if let Some(first) = sum.first_mut() {
            first.set_leading_whitespace(node.leading_whitespace().clone());
        }
        Ok(sum)
    }

    /// `(%index-of item list)` gives the position of the first equal item, or nothing.
    pub(super) fn expand_index_of_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [item, list] = &*params else {
            return Err(error("`%index-of` takes an item, and a list.", node));
        };
        let item = node_text(item)?;
        for (index, other) in list_of(list, node, "The list")?.iter().enumerate() {
            if node_text(other)? == item {
                return Ok(Box::new([number_node(node, index.to_string())]));
            }
        }
        Ok(Box::new([]))
    }

    /// `(%partition f list)` gives `(yes no)`: the items `f` is true for, and the rest.
    pub(super) fn expand_partition_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        let params = self.expand_nodes(params)?;
        let [function, list] = &*params else {
            return Err(error("`%partition` takes a function, and a list.", node));
        };
        let (mut yes, mut no) = (vec![], vec![]);
        for item in list_of(list, node, "The list")? {
            let keep = truthy(&self.call(function, node, std::slice::from_ref(&item))?);
            if keep { yes.push(item) } else { no.push(item) }
        }
        let lists = vec![list_node(node, without_leading(yes)), list_node(node, without_leading(no))];
        Ok(Box::new([list_node(node, spaced(lists))]))
    }

    /// `(%cond (test body...) ...)` expands the body of the first true test,
    /// and nothing if none are. Only that test and body are expanded.
    pub(super) fn expand_cond_macro(&self, node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Expansion<'a> {
        for clause in params {
            let Some(clause) = clause.list() else {
                return Err(error("`%cond` takes clauses `(test body...)`.", clause));
            };
            let items: Vec<ParseNode<'a>> = clause.items().collect();
            let Some((test, body)) = items.split_first() else {
                return Err(error("A `%cond` clause cannot be empty.", node));
            };
            if truthy(&self.expand_node(test)?) {
                let mut expanded = self.expand_nodes(body)?;
                if let Some(first) = expanded.first_mut() {
                    first.set_leading_whitespace(node.leading_whitespace().clone());
                }
                return Ok(expanded);
            }
        }
        Ok(Box::new([]))
    }
}
