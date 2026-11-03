//! Procedural macro for the `arguments! { ... }`
//! macro-argument parser for seam macros.
//! A malformed schema is reported as a compile error at the offending tokens.

use std::{collections::{HashMap, HashSet}, iter::Peekable};

use proc_macro2::{token_stream::IntoIter, Delimiter, Span, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::{self,
    spanned::Spanned,
    Error, Expr, ExprRange, ExprLit,
    Lit, Pat, PatOr,
    RangeLimits,
};

type Result<T> = std::result::Result<T, Error>;

/// Expect the next token to be the punctuation `punct`.
fn expect_punct(token: Option<TokenTree>, punct: char, what: &str) -> Result<()> {
    match token {
        Some(TokenTree::Punct(p)) if p.as_char() == punct => Ok(()),
        Some(token) => Err(Error::new(token.span(), format!("expected `{punct}` {what}"))),
        None => Err(Error::new(Span::call_site(), format!("expected `{punct}` {what}, found end of input"))),
    }
}

#[derive(Clone, Copy)]
enum PositionTypes { Mandatory, Optional, Rest }

#[derive(Clone, Copy)]
enum ParseState {
    ArgumentPosition, //< `mandatory: ...', `optional: ...', `rest: ...'.
    PositionPattern(PositionTypes),  //< pattern for position or name.
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgumentKind {
    Literal,
    String,
    Symbol,
    Number,
    Symbolic,
    List,
    Any,
    None
}

#[derive(Clone)]
struct ArgumentProperties {
    kind: ArgumentKind,
    position_type: PositionTypes,
    rust_type: TokenStream,
}

struct ArgumentStructTypes {
    positional: HashMap<usize, ArgumentProperties>,
    named: HashMap<String, ArgumentProperties>,
    rest: ArgumentProperties,
}

/// Convert an argument keyword (e.g. `allow-html`) into a valid
/// raw Rust identifier (e.g. `r#allow_html`) for the generated struct field.
/// The same type, with the lifetime `'p` of borrowed arguments elided,
/// for use outside of the generated argument struct.
fn elide_borrow(rust_type: &TokenStream) -> TokenStream {
    let mut lifetime = false;
    rust_type.clone().into_iter().map(|token| {
        let token = match token {
            TokenTree::Ident(ident) if lifetime && ident == "p" =>
                TokenTree::Ident(proc_macro2::Ident::new("_", ident.span())),
            TokenTree::Group(group) => {
                let mut elided = proc_macro2::Group::new(group.delimiter(), elide_borrow(&group.stream()));
                elided.set_span(group.span());
                TokenTree::Group(elided)
            },
            token => token,
        };
        lifetime = matches!(&token, TokenTree::Punct(punct) if punct.as_char() == '\'');
        token
    }).collect()
}

fn to_ident(name: &str) -> String {
    // Replace any character that cannot appear in an identifier.
    let mut ident: String = name.chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    // Identifiers cannot start with a digit.
    if ident.starts_with(|c: char| c.is_numeric()) {
        ident.insert(0, '_');
    }
    format!("r#{ident}")
}

/// Macro that generates an argument parser and builds a custom struct
/// holding provided arguments, given a schema and the list of arguments.
/// ### Example
/// ```ignore
/// let (parser, args) = arguments! { [&params]
///     mandatory(1..=3): literal,
///     mandatory(4): number fn(n: ParseNode) {
///         let n = extract_number(n)?;
///         let Ok(n): u32 = n.value.parse() else {
///             return Err("Argument must be an integer.");
///         }
///         if n % 2 == 0 {
///             Ok(())
///         } else {
///             Err("Integer must be even.")
///         }
///     },
///     optional("trailing"): literal["true", "false"],
///     rest: number
/// }?;
/// println!("first  arg {:?}", args.number.1); // a literal (Node<'a>).
/// println!("second arg {:?}", args.number.2); // a literal (Node<'a>).
/// println!("third  arg {:?}", args.number.3); // a literal (Node<'a>).
/// println!("fourth arg {:?}", args.number.4); // an even integer (Node<'a>).
/// if let Some(named) = args.trailing {
///     println!("named arg {:?}", named);  // the literal "true" or "false".
/// }
/// for arg in args.rest {
///     println!("trailing arg: {:?}", arg);  // trailing number args.
/// }
/// ```
#[proc_macro]
pub fn arguments(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    expand(stream.into())
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

fn expand(stream: TokenStream) -> Result<TokenStream> {
    let mut stream = stream.into_iter().peekable();

    // Parse the provided runtime argument vector.
    let params = match stream.next() {
        Some(TokenTree::Group(group)) => group.stream(),
        Some(token) => return Err(Error::new(token.span(),
            "expected the arguments to parse, in brackets, e.g. `[&params]`")),
        None => return Err(Error::new(Span::call_site(),
            "expected the arguments to parse, in brackets, e.g. `[&params]`")),
    };

    // Start building final source-code output.
    let mut out: TokenStream = TokenStream::new();
    out.extend(quote! {
        let mut rules = crate::parse::macros::ArgRules::new();
    });
    // Initialize keeping track of the custom argument struct types.
    let mut arg_struct = ArgumentStructTypes {
        positional: HashMap::new(),
        named: HashMap::new(),
        rest: ArgumentProperties {
            kind: ArgumentKind::None,
            position_type: PositionTypes::Rest,
            rust_type: quote! { () },
        },
    };
    // Parse the argument schema.
    let mut parse_state = ParseState::ArgumentPosition;
    while let Some(token) = stream.next() {
        match parse_state {
            ParseState::ArgumentPosition => match token {
                TokenTree::Ident(ident) => {
                    match ident.to_string().as_str() {
                        "mandatory" => {
                            parse_state = ParseState::PositionPattern(PositionTypes::Mandatory);
                            continue;
                        },
                        "optional" => {
                            parse_state = ParseState::PositionPattern(PositionTypes::Optional);
                            continue;
                        },
                        "rest" => {
                            parse_state = ParseState::PositionPattern(PositionTypes::Rest);
                            continue;
                        },
                        _ => return Err(Error::new(ident.span(),
                            "expected `mandatory`, `optional` or `rest`")),
                    }
                },
                _ => return Err(Error::new(token.span(),
                    "expected `mandatory`, `optional` or `rest`")),
            },
            // Parse `rest: ...`
            ParseState::PositionPattern(PositionTypes::Rest) => {
                // Check we consumed `:`
                expect_punct(Some(token), ':', "after `rest`")?;
                let argument_type = parse_argument_type(&mut stream, PositionTypes::Rest)?;
                let arg_type = argument_type.source_code;
                let code = quote! {{
                    let arg_type = #arg_type;
                    rules.register_remaining(arg_type);
                }};
                out.extend(code);
                // Register argument struct type.
                let rust_type = argument_type.properties.rust_type;
                arg_struct.rest.kind = argument_type.properties.kind;
                arg_struct.rest.rust_type = rust_type;
            },
            ParseState::PositionPattern(pos @
(PositionTypes::Mandatory | PositionTypes::Optional)) => {
                // Parse the pattern for matching argument positions.
                let position_pattern = match token {
                    TokenTree::Group(group) => group.stream(),
                    token => return Err(Error::new(token.span(),
                        "expected a parenthesised pattern matching the argument position, e.g. `(1)` or `(\"name\")`")),
                };
                // Skip `:`
                expect_punct(stream.next(), ':', "after the argument position")?;
                // Register the argument-position matcher.
                let argument_type = parse_argument_type(&mut stream, pos)?;
                let arg_type = argument_type.source_code;
                let arg_pos = match pos {
                    PositionTypes::Mandatory => quote! { crate::parse::macros::Arg::Mandatory },
                    PositionTypes::Optional  => quote! { crate::parse::macros::Arg::Optional  },
                    PositionTypes::Rest => unreachable!(),
                };
                let code = quote! {{
                    let arg_type = #arg_type;
                    let arg = #arg_pos(arg_type);
                    fn position_matcher(pattern: crate::parse::macros::ArgPos<'_>) -> bool {
                        matches!(pattern.into(), Some(#position_pattern))
                    }
                    rules.register(position_matcher, arg);
                }};
                out.extend(code);
                // Register argument struct type.
                let rust_type = argument_type.properties.rust_type;
                let rust_type = match pos {
                    PositionTypes::Mandatory => quote! { #rust_type },
                    PositionTypes::Optional  => quote! { Option<#rust_type> },
                    PositionTypes::Rest => unreachable!(),
                };
                // Take each possible argument position and register the type.
                for position in parse_finite_pattern(position_pattern)? {
                    match position {
                        StringOrInt::String(name) => arg_struct.named.insert(name, ArgumentProperties {
                            kind: argument_type.properties.kind,
                            position_type: pos,
                            rust_type: rust_type.clone(),
                        }),
                        StringOrInt::Int(offset)  => arg_struct.positional.insert(offset, ArgumentProperties {
                            kind: argument_type.properties.kind,
                            position_type: pos,
                            rust_type: rust_type.clone(),
                        }),
                    };
                }
            },
        }
        // Handle switching back states, and any additional delimiting tokens.
        if let ParseState::PositionPattern(_) = parse_state {
            // Finished parsing a pattern, skip the comma delimiting the next rule.
            let token = stream.next();
            // Expecting to find ',' (or the end) at this point.
            if token.is_some() {
                expect_punct(token, ',', "after an argument rule")?;
            }
            // Otherwise, switch back to trying tp parse a new rule.
            parse_state = ParseState::ArgumentPosition;
        }
    }

    // Build tuple type for arguments structure.
    let tuple_len = *arg_struct.positional.keys().max().unwrap_or(&0);
    let mut tuple_types = vec![quote! { () }; tuple_len + 1];
    for (i, tuple_type) in tuple_types.iter_mut().enumerate().skip(1) {
        if let Some(props) = arg_struct.positional.get(&i) {
            *tuple_type = props.rust_type.clone();
        }
    }
    // Build named arguments struct fields.
    let mut named_arguments: Vec<TokenStream> = vec![];
    let mut named_types: Vec<TokenStream> = vec![];
    let mut named_values: Vec<TokenStream> = vec![];
    let mut named_idents: HashMap<String, &String> = HashMap::new();
    for (name, props) in &arg_struct.named {
        let rust_type = props.rust_type.clone();
        let ident = to_ident(name);
        // Distinct keywords (e.g. `a-b` and `a_b`) may map to the same field.
        if let Some(other) = named_idents.insert(ident.clone(), name) {
            return Err(Error::new(Span::call_site(), format!(
                "named arguments `{other}` and `{name}` both map to the field `{ident}`")));
        }
        let variable: TokenStream = ident.parse()?;
        named_types.push(rust_type);
        named_arguments.push(variable);
        match props.position_type {
            PositionTypes::Mandatory => named_values.push(quote! {{
                let retrieved = parser.get(#name)?;
                retrieved
                    .try_into()
                    .expect("node type-checked but unwrap failed")
            }}),
            PositionTypes::Optional => named_values.push(quote! {{
                parser.get_optional(#name).map(|retrieved|
                    retrieved
                        .try_into()
                        .expect("node type-checked but unwrap failed"))
            }}),
            PositionTypes::Rest => unreachable!(),
        }
    }

    let named_elided_types: Vec<TokenStream> = named_types.iter().map(elide_borrow).collect();

    // Generate code for extracting the values of the positional arguments.
    let mut tuple_variables = vec![quote! { () }];
    let mut tuple_variable_initializations = vec![];
    for (i, arg_type) in tuple_types.iter().enumerate().skip(1) {
        let arg_num_name = quote::format_ident!("arg_num_{i}");

        tuple_variables.push(arg_num_name.to_token_stream());
        let Some(props) = arg_struct.positional.get(&i) else { continue };
        let elided = elide_borrow(arg_type);
        match props.position_type {
            PositionTypes::Mandatory => {
                tuple_variable_initializations.push(quote! {
                    let #arg_num_name: #elided = {
                        let retrieved = parser.get(#i)?;
                        retrieved
                            .try_into()
                            .expect("node type-checked but unwrap failed")
                    };
                });
            },
            PositionTypes::Optional => {
                tuple_variable_initializations.push(quote! {
                    let #arg_num_name: #elided = parser
                        .get_optional(#i)
                        .map(|retrieved|
                            retrieved
                                .try_into()
                                .expect("node type-checked but unwrap failed"));
                });
            },
            PositionTypes::Rest => unreachable!(),
        }
    }

    // Generate code for extracting the trailing arguments.
    let rest_rust_type = arg_struct.rest.rust_type;
    let has_rest_capture = arg_struct.rest.kind != ArgumentKind::None;
    let rest_elided = elide_borrow(&rest_rust_type);
    let trailing_arguments = if has_rest_capture {
        quote! {
            {
                parser.trailing
                    .iter()
                    .map(|arg| {
                        let retrieved: #rest_elided = (*arg).try_into().expect("node type-checked but unwrap failed");
                        retrieved
                    })
                    .collect()
            }
        }
    } else {
        quote! { () }
    };

    let rest_struct_decl = if has_rest_capture {
        quote! {rest: Vec<#rest_rust_type>}
    } else {
        quote! {rest: ()}
    };

    // Assemble code that builds argument parser context and argument struct.
    let out = out.into_iter();
    Ok(quote! {
        {
            #(#out)*;
            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug)]
            struct Arguments<'p, 'a> {
                number: (#(#tuple_types),*,),
                #(#named_arguments: #named_types,)*
                #rest_struct_decl,
                _lifetimes: std::marker::PhantomData<(&'p (), &'a ())>,
            }
            let parser_result = crate::parse::macros::ArgParser::new(rules, &node, #params);
            match parser_result {
                Ok(parser) => {
                    #(#tuple_variable_initializations)*
                    #(let #named_arguments: #named_elided_types = #named_values;)*
                    let rest = #trailing_arguments;
                    let args_struct = Arguments {
                        number: (#(#tuple_variables),*,),
                        #(#named_arguments,)*
                        rest,
                        _lifetimes: std::marker::PhantomData,
                    };
                    Ok((parser, args_struct))  // Returns the parser and args from the scope.
                },
                Err(e) => Err(e),
            }
        }
    })
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum StringOrInt { String(String), Int(usize) }

/// Parse a subset of rust "patterns" that have a finite set of
/// values which will satisfy said pattern.
/// Returns a list of all values which may satisfy it.
/// Restrictions:
///  - exact match (`a`)
///  - ranges (`a..b`, `a..=b`);
///  - or-patterns (`expr1 | expr2`);
///  - values are strings or integers (`a: &str` or `a: usize`).
fn parse_finite_pattern(pat: TokenStream) -> Result<HashSet<StringOrInt>> {
    let mut set = HashSet::new();
    // Parse the input TokenStream into a syn::Pat
    let expr = syn::parse::Parser::parse2(Pat::parse_multi, pat)?;

    // Recursively parse patterns.
    fn parse_expr(expr: &Pat, set: &mut HashSet<StringOrInt>) -> Result<()> {
        match expr {
            // Handle literals (integers or strings)
            Pat::Lit(ExprLit { lit, .. }) => {
                match lit {
                    Lit::Int(lit_int) => {
                        set.insert(StringOrInt::Int(lit_int.base10_parse::<usize>()?));
                    }
                    Lit::Str(lit_str) => {
                        set.insert(StringOrInt::String(lit_str.value()));
                    }
                    lit => return Err(Error::new(lit.span(),
                        "argument positions are integers or strings")),
                }
            }
            // Handle ranges
            Pat::Range(ExprRange {
                start: Some(start),
                end: Some(end),
                limits,
                ..
            }) => {
                // Parse the start and end as integers
                let (
                    Expr::Lit(ExprLit { lit: Lit::Int(start_lit), .. }),
                    Expr::Lit(ExprLit { lit: Lit::Int(end_lit), .. }),
                ) = (&**start, &**end) else {
                    return Err(Error::new(expr.span(), "ranges must be between two integers"));
                };
                {
                    let start_val = start_lit.base10_parse::<usize>()?;
                    let end_val = end_lit.base10_parse::<usize>()?;
                    // Enumerate inclusive (`..=`) or exclusive (`..`) range.
                    match limits {
                        RangeLimits::HalfOpen(_) => {
                            for i in start_val..end_val {
                                set.insert(StringOrInt::Int(i));
                            }
                        },
                        RangeLimits::Closed(_) => {
                            for i in start_val..=end_val {
                                set.insert(StringOrInt::Int(i));
                            }
                        },
                    }
                }
            }
            // Handle or-patterns
            Pat::Or(PatOr { cases, .. }) => {
                // For or-patterns, parse both the left and right expressions recursively
                for case in cases {
                    parse_expr(case, set)?;
                }
            }
            _ => return Err(Error::new(expr.span(),
                "expected an integer, a string, a bounded integer range, or `|` between them")),
        }
        Ok(())
    }

    parse_expr(&expr, &mut set)?;
    Ok(set)
}


struct ArgumentType {
    source_code: TokenStream,
    properties: ArgumentProperties,
}

fn parse_argument_type(stream: &mut Peekable<IntoIter>, position_type: PositionTypes) -> Result<ArgumentType> {
    use ArgumentKind as AK;
    let (kind, rust_type, arg_type) = match stream.next() {
        Some(TokenTree::Ident(ident)) => match ident.to_string().as_str() {
            "literal"  => (AK::Literal,  quote! { &'p crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Literal  }),
            "string"   => (AK::String,   quote! { &'p crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::String   }),
            "symbol"   => (AK::Symbol,   quote! { &'p crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Symbol   }),
            "number"   => (AK::Number,   quote! { &'p crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Number   }),
            "symbolic" => (AK::Symbolic, quote! { &'p crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Symbolic }),
            "list" => (AK::List, quote! { &'p [crate::parse::parser::ParseNode<'a>] }, quote! { crate::parse::macros::ArgType::List }),
            "any" => (AK::Any, quote! { &'p crate::parse::parser::ParseNode<'a> }, quote! { crate::parse::macros::ArgType::Any }),
            _ => return Err(Error::new(ident.span(), ARGUMENT_TYPES)),
        },
        Some(token) => return Err(Error::new(token.span(), ARGUMENT_TYPES)),
        None => return Err(Error::new(Span::call_site(), format!("{ARGUMENT_TYPES}, found end of input"))),
    };

    let token = stream.peek().cloned();
    let source_code = match token {
        // Parse a list of potential pattern matches for argument.
        Some(TokenTree::Group(group)) => match group.delimiter() {
            Delimiter::Bracket | Delimiter::Parenthesis => {
                stream.next(); // Consume the list.
                let group = group.stream().into_iter();
                let predicates = group.map(|predicate| match predicate {
                    TokenTree::Literal(literal) => quote! {
                        crate::parse::macros::ArgPredicate::Exactly(String::from(#literal))
                    },
                    token => token.into_token_stream(),
                });
                quote! { #arg_type(vec![ #(#predicates)* ]) }
            },
            _ => return Err(Error::new(group.span(),
                "expected a list of accepted values in brackets, e.g. `[\"true\", \"false\"]`")),
        },
        // Parse a function which matches the argument.
        Some(TokenTree::Ident(ident)) if ident == "fn" => {
            stream.next(); // Consume the `fn` keyword.
            // Consume the function argument list.
            let fn_arguments = match stream.next() {
                Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Parenthesis
                    => group.stream().into_iter(),
                Some(token) => return Err(Error::new(token.span(), "expected the predicate's parameters, e.g. `(n: &ParseNode)`")),
                None => return Err(Error::new(Span::call_site(), "expected the predicate's parameters, found end of input")),
            };
            // Consume the function body.
            let fn_body = match stream.next() {
                Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Brace => group,
                Some(token) => return Err(Error::new(token.span(), "expected the predicate's body in braces")),
                None => return Err(Error::new(Span::call_site(), "expected the predicate's body, found end of input")),
            };
            quote! {{
                fn predicate<'tree>(#(#fn_arguments),*) -> Result<(), ExpansionError<'tree>> { #fn_body }
                let arg_pred = crate::parse::macros::ArgPredicate::Satisfying(predicate);
                #arg_type(vec![arg_pred])
            }}
        }
        _ => quote! { #arg_type(vec![]) },
    };

    Ok(ArgumentType {
        source_code,
        properties: ArgumentProperties {
            kind,
            position_type,
            rust_type,
        },
    })
}

const ARGUMENT_TYPES: &str = "expected an argument type: \
    `literal`, `string`, `symbol`, `number`, `symbolic`, `list` or `any`";
