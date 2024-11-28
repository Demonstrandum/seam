//! Procedural macro for the `arguments! { ... }`
//! macro-argument parser for seam macros.
//! TODO: Convert all `panic!(..)` calls to actual compiler errors.

use std::{collections::{HashMap, HashSet}, iter::Peekable};

use proc_macro;
use proc_macro2::{token_stream::IntoIter, Delimiter, TokenStream, TokenTree};
use quote::quote;
use syn::{self,
    Expr, ExprRange, ExprLit,
    Lit, Pat, PatOr,
    RangeLimits,
};

#[derive(Clone, Copy)]
enum PositionTypes { Mandatroy, Optional, Rest }

#[derive(Clone, Copy)]
enum ParseState {
    ArgumentPosition, //< `mandatory: ...', `optional: ...', `rest: ...'.
    PositionPattern(PositionTypes),  //< pattern for position or name.
}

#[derive(Clone)]
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

/// Macro that generates an argument parser and builds a custom struct
/// holding provided arguments, given a schema and the list of arguments.
/// Example:
///     ```
///     let (parser, args) = arguments! { [&params]
///         mandatory(1..=3): literal,
///         mandatory(4): number fn(_v: ParseNode) { true },
///         optional("trailing"): literal["true", "false"],
///         rest: number
///     }?;
///     println!("first  arg {:?}", args.number.1); // a literal (Node<'a>).
///     println!("second arg {:?}", args.number.2); // a literal (Node<'a>).
///     println!("third  arg {:?}", args.number.3); // a literal (Node<'a>).
///     println!("fourth arg {:?}", args.number.4); // a number of any kind (Node<'a>).
///     if let Some(named) = args.trailing {
///         println!("named arg {:?}", named);  // the literal "true" or "false".
///     }
///     for arg in args.rest {
///         println!("trailing arg: {:?}", arg);  // trailing number args.
///     }
///     ```
#[proc_macro]
pub fn arguments(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let stream: TokenStream = stream.into();
    let stream = stream.into_iter().peekable();
    let mut stream = stream.into_iter();

    // Parse the provided runtime argument vector.
    let Some(args_vec) = stream.next().and_then(|tokens| match tokens {
        TokenTree::Group(group) => match
            group.stream()
                .into_iter()
                .collect::<Vec<TokenTree>>()
                .as_slice()
        {
            [params,] => Some(params.clone()),
            _ => None,
        },
        _ => None,
    }) else {
        panic!("Vector of arguments not given.");
    };

    // Start building final source-code output.
    let mut out: TokenStream = TokenStream::new();
    out.extend(quote! {
        let mut rules = crate::parse::macros::ArgRules::new();
        let params: Vec<crate::parse::parser::ParseNode> = #args_vec;
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
                            parse_state = ParseState::PositionPattern(PositionTypes::Mandatroy);
                        },
                        "optional" => {
                            parse_state = ParseState::PositionPattern(PositionTypes::Optional);
                        },
                        "rest" => {
                            parse_state = ParseState::PositionPattern(PositionTypes::Rest);
                        },
                        _ => panic!("Invalid token: `{}`", ident.to_string()),
                    }
                },
                _ => panic!("Invalid token: `{}`", token),
            },
            // Parse `rest: ...`
            ParseState::PositionPattern(PositionTypes::Rest) => {
                // Check we consumed `:`
                match token {
                    TokenTree::Punct(punct) => assert!(punct.as_char() == ':'),
                    _ => panic!("Invalid token: `{}`", token),
                }
                let argument_type = parse_argument_type(&mut stream, PositionTypes::Rest);
                let arg_type = argument_type.source_code;
                let code = quote! {{
                    let arg_type = #arg_type;
                    rules.register_remaining(arg_type);
                }};
                out.extend(code);
                // Register argument struct type.
                let rust_type = argument_type.properties.rust_type;
                arg_struct.rest.kind = argument_type.properties.kind;
                arg_struct.rest.rust_type = quote! { Vec<#rust_type> };
            },
            ParseState::PositionPattern(pos@PositionTypes::Mandatroy | pos@PositionTypes::Optional) => {
                // Parse the pattern for matching argument positions.
                let position_pattern = match token {
                    TokenTree::Group(group) => group.stream(),
                    _ => panic!("Unexpected token"),
                };
                // Skip `:`
                let token = stream.next();
                match token {
                    Some(TokenTree::Punct(punct)) => assert!(punct.as_char() == ':'),
                    _ => panic!("Invalid token: `{:?}`", token),
                }
                // Register the argument-position matcher.
                let argument_type = parse_argument_type(&mut stream, pos);
                let arg_type = argument_type.source_code;
                let arg_pos = match pos {
                    PositionTypes::Mandatroy => quote! { crate::parse::macros::Arg::Mandatory },
                    PositionTypes::Optional  => quote! { crate::parse::macros::Arg::Optional  },
                    _ => unreachable!(),
                };
                let code = quote! {{
                    let arg_type = #arg_type;
                    let arg_pos = #arg_pos;
                    fn position_matcher(pattern: &Box<dyn crate::parse::macros::ArgMatcher>) -> bool {
                        match pattern.into() {
                            Some(#position_pattern) => true,
                            _ => false,
                        }
                    }
                    rules.register(position_matcher, arg);
                }};
                out.extend(code);
                // Register argument struct type.
                let rust_type = argument_type.properties.rust_type;
                let rust_type = match pos {
                    PositionTypes::Mandatroy => quote! { #rust_type },
                    PositionTypes::Optional  => quote! { Option<#rust_type> },
                    _ => unreachable!(),
                };
                // Take each possible argument position and register the type.
                for position in parse_finite_pattern(position_pattern) {
                    match position {
                        StringOrInt::String(name) => arg_struct.named.insert(name, ArgumentProperties {
                            kind: argument_type.properties.kind,
                            position_type: pos,
                            rust_type,
                        }),
                        StringOrInt::Int(offset)  => arg_struct.positional.insert(offset, ArgumentProperties {
                            kind: argument_type.properties.kind,
                            position_type: pos,
                            rust_type,
                        }),
                    };
                }
            },
        };
    }

    // Build tuple type for arguments structure.
    let tuple_len = *arg_struct.positional.keys().max().unwrap_or(&0);
    let mut tuple_types = vec![quote! { () }; tuple_len];
    for i in 0..tuple_len {
        tuple_types.push(match arg_struct.positional.remove(&i) {
            Some(props) => props.rust_type,
            None            => quote! { () },
        });
    }
    // Build named arguments struct fields.
    let mut named_arguments: Vec<TokenStream> = vec![];
    for (name, props) in arg_struct.named.iter() {
        let rust_type = props.rust_type;
        named_arguments.push(quote! {
            #name: #rust_type
        });
    }

    // TODO: need to iterate the runtime-provided params and extract
    // them into the correct type depending on expected type
    // (i.e. literal => Node<'a>; list => Vec<ParseNode<'a>; etc.)
    // A failure of the above extraction should nicely hand back a
    // custom Err() message.
    // Optional nodes do not fail, they just get a `None` value.
    // While doing this, each extracted argument should be checked
    // that it satisfies the supplemental conditions in the schema (predicates).
    // Again, if it fails the check, default on an Err() describing in the
    // most informative possible way why it failed.
    // Finally, no failures should mean a fully populated arguments struct
    // can be constructed from the previous arguments, and can be returned.

    // TODO: write reusable `extract_literal` function
    // (signature: ParseNode<'a> -> Result<Node<'a>, ExpansionError<'a>>)
    // that will give a custom error message for failing to extract.
    // e.g. "expected a literal, got a {insert_node_kind}".

    for i in 1..=tuple_len {
        let arg_num_name: TokenStream = format!("arg_num_{}", i).parse().unwrap();

        let code = quote! {
            let #arg_num_name = parser.positional.get();
        };
    }

    // Assemble code that builds argument parser context and argument struct.
    let rest_rust_type = arg_struct.rest;
    let out = out.into_iter();
    quote! {
        {
            #(#out)*;
            struct MyArguments {
                number: #(#tuple_types),*,
                #(#named_arguments),*,
                rest: #rest_rust_type,
            }
            let rules = rules.clone();
            match crate::parse::macros::ArgParser::new(rules, params) {
                Ok(parser) => {
                    let args_struct = MyArguments {
                        ...
                    };
                    Ok((parser, args_struct))  // Returns the parser and args from the scope.
                },
                Err(e) => e,
            }
        }
    }.into()
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
/// TODO: Re-emit the pattern converted as such:
///   `2..=4 | "hello" | 5` => `Int(2..=4) | String(&'static "hello") | Int(5)`
fn parse_finite_pattern(pat: TokenStream) -> HashSet<StringOrInt> {
    let mut set = HashSet::new();
    // Parse the input TokenStream into a syn::Pat
    let expr = syn::parse::Parser::parse2(|input: syn::parse::ParseStream| {
        Pat::parse_multi(input)
    }, pat.into()).expect("failed");

    // Recursively parse patterns.
    fn parse_expr(expr: &Pat, set: &mut HashSet<StringOrInt>) {
        match expr {
            // Handle literals (integers or strings)
            Pat::Lit(ExprLit { lit, .. }) => {
                match lit {
                    Lit::Int(lit_int) => {
                        set.insert(StringOrInt::Int(lit_int.base10_parse::<usize>().unwrap()));
                    }
                    Lit::Str(lit_str) => {
                        set.insert(StringOrInt::String(lit_str.value()));
                    }
                    _ => {}
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
                if let (
                    Expr::Lit(ExprLit { lit: Lit::Int(start_lit), .. }),
                     Expr::Lit(ExprLit { lit: Lit::Int(end_lit), .. }),
                ) = (&**start, &**end) {
                    let start_val = start_lit.base10_parse::<usize>().unwrap();
                    let end_val = end_lit.base10_parse::<usize>().unwrap();
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
                    };
                }
            }
            // Handle or-patterns
            Pat::Or(PatOr { cases, .. }) => {
                // For or-patterns, parse both the left and right expressions recursively
                for case in cases {
                    parse_expr(case, set);
                }
            }
            _ => panic!("Unsupported pattern.")
        }
    }

    parse_expr(&expr, &mut set);
    set
}


struct ArgumentType {
    source_code: TokenStream,
    properties: ArgumentProperties,
}

fn parse_argument_type(stream: &mut Peekable<IntoIter>, position_type: PositionTypes) -> ArgumentType {
    use ArgumentKind as AK;
    let (kind, rust_type, arg_type) = match stream.next() {
        Some(TokenTree::Ident(ident)) => match ident.to_string().as_str() {
            "literal"  => (AK::Literal,  quote! { crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Literal  }),
            "string"   => (AK::String,   quote! { crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::String   }),
            "symbol"   => (AK::Symbol,   quote! { crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Symbol   }),
            "number"   => (AK::Number,   quote! { crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Number   }),
            "symbolic" => (AK::Symbolic, quote! { crate::parse::parser::Node<'a> }, quote! { crate::parse::macros::ArgType::Symbolic }),
            "list" => (AK::List, quote! { Vec<crate::parse::parser::Node<'a>> }, quote! { crate::parse::macros::ArgType::List }),
            "any" => (AK::Any, quote! { crate::parse::parser::ParseNode<'a> }, quote! { crate::parse::macros::ArgType::Any }),
            _ => panic!("Invalid argument type: `{}`", ident),
        },
        None => panic!("Unexpected EOF"),
        _ => panic!("Invalid token type"),
    };

    let token = stream.peek().map(|token| token.clone());
    let source_code = match token {
        // Parse a list of potential pattern matches for argument.
        Some(TokenTree::Group(group)) => match group.delimiter() {
            Delimiter::Bracket | Delimiter::Parenthesis => {
                stream.next(); // Consume the list.
                let group = group.stream().into_iter();
                quote! { #arg_type(vec![ #(#group),* ]) }
            },
            _ => panic!("Unexpected list delimiter"),
        },
        // Parse a function which matches the arguemnt.
        Some(TokenTree::Ident(ident)) if ident.to_string() == "fn" => {
            stream.next(); // Consume the `fn` keyword.
            let fn_arguments = match stream.next() {
                Some(TokenTree::Group(group)) => group.stream().into_iter(),
                None => panic!("Unexpected EOF"),
                _ => panic!("Unexpected token"),
            };
            let Some(fn_body) = stream.next() else { panic!("Unexpected EOF") };
            quote! {{
                fn predicate(#(#fn_arguments),*) -> bool { #fn_body }
                let arg_pred = crate::parse::macros::ArgPredicate::Satisfying(Box::new(predicate));
                #arg_type(vec![arg_pred])
            }}
        }
        _ => quote! { #arg_type(vec![]) },
    };

    ArgumentType {
        source_code,
        properties: ArgumentProperties {
            kind,
            position_type,
            rust_type,
        },
    }
}
