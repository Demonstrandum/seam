//! The items of a list node. A list made by a macro such as `%range`,
//! `%take` or `%concat` may be *lazy*: only a description of its items,
//! which are made one at a time when asked for. Nothing about this is
//! visible in the language, as the items are realised (made and kept)
//! as soon as anything needs them all at once, as a slice.
use std::{cell::OnceCell, fmt, ops::{Deref, DerefMut}, rc::Rc};

use super::{parser::{Node, ParseNode}, tokens::Site};

/// The items of a list node, realised or lazy.
/// Dereferences to a slice of its items, realising them if need be,
/// while [`List::len`], [`List::item`] and [`List::items`] do not.
#[derive(Clone)]
pub struct List<'a>(Items<'a>);

#[derive(Clone)]
enum Items<'a> {
    Realised(Box<[ParseNode<'a>]>),
    Lazy(Rc<Lazy<'a>>),
}

struct Lazy<'a> {
    source: Source<'a>,
    len: usize,
    realised: OnceCell<Box<[ParseNode<'a>]>>,
}

/// What a lazy list's items are made from.
enum Source<'a> {
    /// Numbers `first`, `first + step`, ...
    Range { first: Step, site: Site<'a> },
    /// Items of a list from `start`, the first without leading whitespace.
    Slice { list: List<'a>, start: usize },
    /// Items of a list backwards, but with the whitespace in its order.
    Reverse(List<'a>),
    /// Items of each list in turn, each list's first item at least spaced.
    Chain(Box<[List<'a>]>),
}

/// The first number, and step, of a range.
#[derive(Debug, Clone, Copy)]
pub enum Step {
    Int(i64, i64),
    Float(f64, f64),
}

impl Step {
    #[allow(clippy::cast_precision_loss)]
    fn nth(self, n: usize) -> String {
        let float = |first: f64, step: f64| (first + step * n as f64).to_string();
        match self {
            Self::Int(first, step) => i64::try_from(n).ok()
                .and_then(|n| step.checked_mul(n))
                .and_then(|offset| first.checked_add(offset))
                .map_or_else(|| float(first as f64, step as f64), |int| int.to_string()),
            Self::Float(first, step) => float(first, step),
        }
    }
}

impl<'a> List<'a> {
    fn lazy(source: Source<'a>, len: usize) -> Self {
        Self(Items::Lazy(Rc::new(Lazy { source, len, realised: OnceCell::new() })))
    }

    /// `len` numbers counting from `first` by `step`.
    #[must_use]
    pub fn range(step: Step, len: usize, site: Site<'a>) -> Self {
        Self::lazy(Source::Range { first: step, site }, len)
    }

    /// The items from `start`, up to `len` of them.
    #[must_use]
    pub fn slice(&self, start: usize, len: usize) -> Self {
        let start = start.min(self.len());
        let len = len.min(self.len() - start);
        // A slice of a slice is a slice of the original.
        if let Items::Lazy(lazy) = &self.0 && let Source::Slice { list, start: offset } = &lazy.source {
            return list.slice(offset + start, len);
        }
        Self::lazy(Source::Slice { list: self.clone(), start }, len)
    }

    /// The items backwards, keeping the whitespace between them in order.
    #[must_use]
    pub fn reverse(&self) -> Self {
        Self::lazy(Source::Reverse(self.clone()), self.len())
    }

    /// The items of each list in turn.
    #[must_use]
    pub fn chain(lists: Vec<Self>) -> Self {
        let len = lists.iter().map(List::len).sum();
        Self::lazy(Source::Chain(lists.into_boxed_slice()), len)
    }

    /// Number of items, without realising them.
    #[must_use]
    pub fn len(&self) -> usize {
        match &self.0 {
            Items::Realised(nodes) => nodes.len(),
            Items::Lazy(lazy) => lazy.len,
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// The item at an index, without realising the others.
    #[must_use]
    pub fn item(&self, index: usize) -> Option<ParseNode<'a>> {
        let lazy = match &self.0 {
            Items::Realised(nodes) => return nodes.get(index).cloned(),
            Items::Lazy(lazy) if index >= lazy.len => return None,
            Items::Lazy(lazy) => lazy,
        };
        if let Some(nodes) = lazy.realised.get() {
            return nodes.get(index).cloned();
        }
        Some(match &lazy.source {
            Source::Range { first, site } => {
                let whitespace = if index == 0 { "" } else { " " };
                ParseNode::Number(Node::new(first.nth(index), site, whitespace))
            },
            Source::Slice { list, start } => {
                let mut item = list.item(start + index)?;
                if index == 0 {
                    item.set_leading_whitespace("");
                }
                item
            },
            Source::Reverse(list) => {
                let mut item = list.item(lazy.len - 1 - index)?;
                item.set_leading_whitespace(list.item(index)?.leading_whitespace().clone());
                item
            },
            Source::Chain(lists) => {
                // Items after the first are spaced apart, even where lists meet.
                let mut offset = index;
                for list in lists {
                    if offset < list.len() {
                        let mut item = list.item(offset)?;
                        if index > 0 && offset == 0 && item.leading_whitespace().is_empty() {
                            item.set_leading_whitespace(" ");
                        }
                        return Some(item);
                    }
                    offset -= list.len();
                }
                return None;
            },
        })
    }

    /// Each item in turn, made as it is needed, without realising the list.
    pub fn items(&self) -> impl Iterator<Item = ParseNode<'a>> + '_ {
        (0..self.len()).filter_map(|index| self.item(index))
    }

    /// The items, as a vector.
    #[must_use]
    pub fn into_vec(self) -> Vec<ParseNode<'a>> {
        match self.0 {
            Items::Realised(nodes) => nodes.into_vec(),
            Items::Lazy(_) => self.to_vec(),
        }
    }
}

impl<'a> Deref for List<'a> {
    type Target = [ParseNode<'a>];

    fn deref(&self) -> &Self::Target {
        match &self.0 {
            Items::Realised(nodes) => nodes,
            Items::Lazy(lazy) => lazy.realised.get_or_init(|| self.items().collect()),
        }
    }
}

impl DerefMut for List<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        if let Items::Lazy(_) = self.0 {
            self.0 = Items::Realised(self.to_vec().into_boxed_slice());
        }
        let Items::Realised(nodes) = &mut self.0 else { unreachable!() };
        nodes
    }
}

impl<'a> From<Box<[ParseNode<'a>]>> for List<'a> {
    fn from(nodes: Box<[ParseNode<'a>]>) -> Self { Self(Items::Realised(nodes)) }
}

impl<'a> From<Vec<ParseNode<'a>>> for List<'a> {
    fn from(nodes: Vec<ParseNode<'a>>) -> Self { nodes.into_boxed_slice().into() }
}

impl<'a> FromIterator<ParseNode<'a>> for List<'a> {
    fn from_iter<I: IntoIterator<Item = ParseNode<'a>>>(items: I) -> Self {
        items.into_iter().collect::<Box<[_]>>().into()
    }
}

impl Default for List<'_> {
    fn default() -> Self { Self(Items::Realised(Box::default())) }
}

impl PartialEq for List<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && **self == **other
    }
}

impl fmt::Debug for List<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'l, 'a> IntoIterator for &'l List<'a> {
    type Item = &'l ParseNode<'a>;
    type IntoIter = std::slice::Iter<'l, ParseNode<'a>>;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}
