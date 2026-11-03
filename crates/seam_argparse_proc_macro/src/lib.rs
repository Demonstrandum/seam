//! Procedural macro for the `arguments! { ... }`
//! macro-argument parser for seam macros.
//! A malformed schema is reported as a compile error at the offending tokens.

use std::collections::BTreeMap;

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    braced, bracketed, parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned,
    token, Block, Error, Expr, ExprLit, ExprRange, FnArg, Ident, Lit, LitStr, Pat, PatOr,
    RangeLimits, Result, Token,
};

/// Macro that generates an argument parser for a seam macro call,
/// returning a struct holding the arguments, given a schema.
/// ### Example
/// ```ignore
/// let args = arguments! { node, &params;
///     mandatory(1..=3): literal,
///     mandatory(4): number fn(n: &ParseNode<'t>) {
///         match n.atomic().map(|n| n.value.parse::<u32>()) {
///             Some(Ok(n)) if n % 2 == 0 => Ok(()),
///             _ => Err(ExpansionError::new("Integer must be even.", n.site())),
///         }
///     },
///     optional("trailing"): literal["true", "false"],
///     rest: number,
/// }?;
/// println!("first  arg {:?}", args.number.1); // a literal (&Node<'a>).
/// println!("fourth arg {:?}", args.number.4); // an even integer (&Node<'a>).
/// if let Some(named) = args.trailing {
///     println!("named arg {:?}", named);  // the literal "true" or "false".
/// }
/// for arg in args.rest {
///     println!("trailing arg: {:?}", arg);  // trailing number args.
/// }
/// ```
/// `node` is the macro call (for errors), `&params` its arguments.
/// Named arguments are fields named after their keyword (`-` becomes `_`).
#[proc_macro]
pub fn arguments(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let schema = parse_macro_input!(stream as Schema);
    schema.generate()
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

struct Schema {
    node: Expr,
    params: Expr,
    rules: Punctuated<Rule, Token![,]>,
}

enum Position { Mandatory, Optional }

enum Rule {
    /// `mandatory(<pattern>): <type>` or `optional(<pattern>): <type>`.
    Positioned { position: Position, pattern: Pat, kind: ArgKind },
    /// `rest: <type>`.
    Rest(ArgKind),
}

struct ArgKind {
    ident: Ident,
    /// `literal["a", "b"]`.
    one_of: Vec<LitStr>,
    /// `number fn(n: &ParseNode<'t>) { ... }`.
    predicate: Option<(Punctuated<FnArg, Token![,]>, Block)>,
}

impl Parse for Schema {
    fn parse(input: ParseStream) -> Result<Self> {
        let node = input.parse()?;
        input.parse::<Token![,]>()?;
        let params = input.parse()?;
        input.parse::<Token![;]>()?;
        let rules = Punctuated::parse_terminated(input)?;
        Ok(Self { node, params, rules })
    }
}

impl Parse for Rule {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        let position = match ident.to_string().as_str() {
            "rest" => {
                input.parse::<Token![:]>()?;
                return Ok(Self::Rest(input.parse()?));
            },
            "mandatory" => Position::Mandatory,
            "optional" => Position::Optional,
            _ => return Err(Error::new(ident.span(), "expected `mandatory`, `optional` or `rest`")),
        };
        let pattern;
        parenthesized!(pattern in input);
        let pattern = Pat::parse_multi(&pattern)?;
        input.parse::<Token![:]>()?;
        Ok(Self::Positioned { position, pattern, kind: input.parse()? })
    }
}

const ARGUMENT_TYPES: [&str; 7] = ["literal", "string", "symbol", "number", "symbolic", "list", "any"];

impl Parse for ArgKind {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        if !ARGUMENT_TYPES.contains(&ident.to_string().as_str()) {
            return Err(Error::new(ident.span(), format!(
                "expected an argument type: `{}`", ARGUMENT_TYPES.join("`, `"))));
        }
        let mut one_of = vec![];
        if input.peek(token::Bracket) {
            let values;
            bracketed!(values in input);
            one_of = Punctuated::<LitStr, Token![,]>::parse_terminated(&values)?
                .into_iter().collect();
        }
        let mut predicate = None;
        if input.peek(Token![fn]) {
            input.parse::<Token![fn]>()?;
            let arguments;
            parenthesized!(arguments in input);
            let arguments = Punctuated::parse_terminated(&arguments)?;
            let body;
            let brace = braced!(body in input);
            let stmts = body.call(Block::parse_within)?;
            predicate = Some((arguments, Block { brace_token: brace, stmts }));
        }
        Ok(Self { ident, one_of, predicate })
    }
}

/// An argument position, positional or named.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Key { Int(usize), Str(String) }

/// All the positions a pattern matches. It must match a finite set:
/// integers, strings, bounded integer ranges, and `|` between them.
fn pattern_keys(pattern: &Pat, keys: &mut Vec<Key>) -> Result<()> {
    match pattern {
        Pat::Lit(ExprLit { lit: Lit::Int(int), .. }) => keys.push(Key::Int(int.base10_parse()?)),
        Pat::Lit(ExprLit { lit: Lit::Str(string), .. }) => keys.push(Key::Str(string.value())),
        Pat::Range(ExprRange { start: Some(start), end: Some(end), limits, .. }) => {
            let (
                Expr::Lit(ExprLit { lit: Lit::Int(start), .. }),
                Expr::Lit(ExprLit { lit: Lit::Int(end), .. }),
            ) = (&**start, &**end) else {
                return Err(Error::new(pattern.span(), "ranges must be between two integers"));
            };
            let (start, end): (usize, usize) = (start.base10_parse()?, end.base10_parse()?);
            match limits {
                RangeLimits::HalfOpen(_) => keys.extend((start..end).map(Key::Int)),
                RangeLimits::Closed(_) => keys.extend((start..=end).map(Key::Int)),
            }
        },
        Pat::Or(PatOr { cases, .. }) => for case in cases {
            pattern_keys(case, keys)?;
        },
        _ => return Err(Error::new(pattern.span(),
            "expected an integer, a string, a bounded integer range, or `|` between them")),
    }
    Ok(())
}

impl ArgKind {
    /// The constant `ArgRule` checking this kind of argument.
    fn rule(&self) -> TokenStream {
        let kind = format_ident!("{}", capitalise(&self.ident.to_string()), span = self.ident.span());
        let one_of = &self.one_of;
        let satisfying = if let Some((arguments, body)) = &self.predicate {
            quote! {{
                fn predicate<'t>(#arguments) -> Result<(), crate::parse::expander::ExpansionError<'t>> #body
                Some(predicate)
            }}
        } else {
            quote! { None }
        };
        quote! {
            crate::parse::macros::ArgRule {
                kind: crate::parse::macros::ArgType::#kind,
                one_of: &[#(#one_of),*],
                satisfying: #satisfying,
            }
        }
    }

    /// The type an argument of this kind is given as.
    fn rust_type(&self) -> TokenStream {
        match self.ident.to_string().as_str() {
            "list" => quote! { &'p [crate::parse::parser::ParseNode<'a>] },
            "any" => quote! { &'p crate::parse::parser::ParseNode<'a> },
            _ => quote! { &'p crate::parse::parser::Node<'a> },
        }
    }
}

fn capitalise(word: &str) -> String {
    let mut chars = word.chars();
    chars.next().map_or_else(String::new, |first| first.to_uppercase().chain(chars).collect())
}

/// Field name for a named argument, e.g. `allow-html` -> `allow_html`.
fn field_name(name: &str, span: Span) -> Result<Ident> {
    let mut ident: String = name.chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    // Identifiers cannot start with a digit.
    if ident.starts_with(|c: char| c.is_numeric()) {
        ident.insert(0, '_');
    }
    if matches!(ident.as_str(), "number" | "rest" | "_lifetimes") {
        return Err(Error::new(span, format!("named argument `{name}` clashes with the `{ident}` field")));
    }
    syn::parse_str::<Ident>(&ident)
        .or_else(|_| syn::parse_str::<Ident>(&format!("r#{ident}")))
        .map_err(|_| Error::new(span, format!("named argument `{name}` cannot be a field name")))
}

struct Argument<'s> {
    mandatory: bool,
    kind: &'s ArgKind,
    span: Span,
}

impl Schema {
    fn generate(&self) -> Result<TokenStream> {
        // Gather each position's argument rule.
        let mut positional: BTreeMap<usize, Argument> = BTreeMap::new();
        let mut named: BTreeMap<String, Argument> = BTreeMap::new();
        let mut rest: Option<&ArgKind> = None;
        for rule in &self.rules {
            match rule {
                Rule::Rest(kind) => {
                    if rest.replace(kind).is_some() {
                        return Err(Error::new(kind.ident.span(), "`rest` is given more than once"));
                    }
                },
                Rule::Positioned { position, pattern, kind } => {
                    let mut keys = vec![];
                    pattern_keys(pattern, &mut keys)?;
                    for key in keys {
                        let argument = Argument {
                            mandatory: matches!(position, Position::Mandatory),
                            kind,
                            span: pattern.span(),
                        };
                        let repeated = match key {
                            Key::Int(0) => return Err(Error::new(pattern.span(), "positions start from 1")),
                            Key::Int(i) => positional.insert(i, argument).is_some(),
                            Key::Str(name) => named.insert(name, argument).is_some(),
                        };
                        if repeated {
                            return Err(Error::new(pattern.span(), "this argument position is already given a rule"));
                        }
                    }
                },
            }
        }

        // Positional arguments are stored in a tuple, indexed from 1.
        let last = positional.keys().max().copied().unwrap_or(0);
        let mut tuple_types = vec![quote! { () }];
        let mut tuple_values = vec![quote! { () }];
        let mut slots = vec![];
        let mut positional_arms = vec![];
        let mut finish = vec![];
        for i in 1..=last {
            let Some(argument) = positional.get(&i) else {
                tuple_types.push(quote! { () });
                tuple_values.push(quote! { () });
                continue;
            };
            let slot = format_ident!("arg_{i}");
            let rule = argument.kind.rule();
            let rust_type = argument.kind.rust_type();
            slots.push(quote! { let mut #slot: Option<&'p ParseNode<'a>> = None; });
            positional_arms.push(quote! {
                #i => { const RULE: ArgRule = #rule; RULE.check(param)?; #slot = Some(param); },
            });
            if argument.mandatory {
                tuple_types.push(rust_type);
                finish.push(quote! {
                    let Some(#slot) = #slot else {
                        return Err(crate::parse::macros::missing_positional(node, params, #i));
                    };
                });
                tuple_values.push(quote! { #slot.try_into().expect("argument type was checked") });
            } else {
                tuple_types.push(quote! { Option<#rust_type> });
                tuple_values.push(quote! { #slot.map(|arg| arg.try_into().expect("argument type was checked")) });
            }
        }

        // Named arguments become fields named after their keyword.
        let mut fields = vec![];
        let mut field_types = vec![];
        let mut field_values = vec![];
        let mut named_arms = vec![];
        for (name, argument) in &named {
            let field = field_name(name, argument.span)?;
            // Kept apart from the parser's own variables.
            let slot = format_ident!("named_{}", field.to_string().trim_start_matches("r#"));
            let rule = argument.kind.rule();
            let rust_type = argument.kind.rust_type();
            slots.push(quote! { let mut #slot: Option<&'p ParseNode<'a>> = None; });
            named_arms.push(quote! {
                #name => {
                    const RULE: ArgRule = #rule;
                    RULE.check(value)?;
                    if #slot.replace(value).is_some() {
                        return Err(crate::parse::macros::repeated_named(param, #name));
                    }
                },
            });
            if argument.mandatory {
                field_types.push(rust_type);
                finish.push(quote! {
                    let Some(#slot) = #slot else {
                        return Err(crate::parse::macros::missing_named(node, params, #name));
                    };
                });
                field_values.push(quote! { #slot.try_into().expect("argument type was checked") });
            } else {
                field_types.push(quote! { Option<#rust_type> });
                field_values.push(quote! { #slot.map(|arg| arg.try_into().expect("argument type was checked")) });
            }
            fields.push(field);
        }

        // Anything else is a trailing argument, if they are accepted.
        let (rest_type, rest_slot, rest_value, unexpected_positional, unexpected_named) = match rest {
            Some(kind) => {
                let rule = kind.rule();
                let rust_type = kind.rust_type();
                let accept = quote! {{ const RULE: ArgRule = #rule; RULE.check(param)?; rest.push(param); }};
                (
                    quote! { Vec<#rust_type> },
                    quote! { let mut rest: Vec<&'p ParseNode<'a>> = Vec::new(); },
                    quote! { rest.into_iter().map(|arg| arg.try_into().expect("argument type was checked")).collect() },
                    accept.clone(),
                    accept,
                )
            },
            None => (
                quote! { () },
                quote! {},
                quote! { () },
                quote! { return Err(crate::parse::macros::unexpected_positional(param, position)) },
                quote! { return Err(crate::parse::macros::unexpected_named(param, keyword)) },
            ),
        };

        let (node, params) = (&self.node, &self.params);
        Ok(quote! {{
            use crate::parse::{macros::ArgRule, parser::ParseNode};
            #[derive(Debug)]
            struct Arguments<'p, 'a> {
                number: (#(#tuple_types,)*),
                #(#fields: #field_types,)*
                rest: #rest_type,
                _lifetimes: std::marker::PhantomData<(&'p (), &'a ())>,
            }
            #[allow(unused_variables, unused_mut, clippy::match_single_binding)]
            fn parse<'p, 'a>(node: &'p ParseNode<'a>, params: &'p [ParseNode<'a>])
            -> Result<Arguments<'p, 'a>, crate::parse::expander::ExpansionError<'a>> {
                #(#slots)*
                #rest_slot
                let mut position = 0;
                for param in params {
                    if let ParseNode::Attribute { keyword, node: value, .. } = param {
                        match keyword.as_ref() {
                            #(#named_arms)*
                            _ => #unexpected_named,
                        }
                    } else {
                        position += 1;
                        match position {
                            #(#positional_arms)*
                            _ => #unexpected_positional,
                        }
                    }
                }
                #(#finish)*
                Ok(Arguments {
                    number: (#(#tuple_values,)*),
                    #(#fields: #field_values,)*
                    rest: #rest_value,
                    _lifetimes: std::marker::PhantomData,
                })
            }
            parse(#node, #params)
        }})
    }
}
