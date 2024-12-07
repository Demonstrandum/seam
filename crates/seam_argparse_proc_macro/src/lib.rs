//! Procedural macro for the `arguments! { ... }`
//! macro-argument parser for seam macros.
//! TODO: Convert all `panic!(..)` calls to actual compiler errors.
#![feature(proc_macro_span)]
#![feature(proc_macro_diagnostic)]

use std::{collections::{HashMap, HashSet}, iter::Peekable};

use proc_macro::{self, Diagnostic, Span};
use proc_macro2::{token_stream::IntoIter, Delimiter, TokenStream, TokenTree};
use quote::{quote, ToTokens};
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
    let stream: TokenStream = stream.into();
    let stream = stream.into_iter().peekable();
    let mut stream = stream.into_iter();

    let struct_name: TokenStream = format!("MyArgs_{}", Span::call_site().line()).parse().unwrap();

    // Parse the provided runtime argument vector.
    let Some(args_vec) = stream.next().and_then(|tokens| match tokens {
        TokenTree::Group(group) => Some(group
            .stream()
            .into_iter()
            .collect::<Vec<TokenTree>>()
            .as_slice()
            .to_vec()),
        _ => None,
    }) else {
        panic!("Argument vector not given.");
    };
    let params: TokenStream = quote! { #(#args_vec)* };

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
                            parse_state = ParseState::PositionPattern(PositionTypes::Mandatroy);
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
                arg_struct.rest.rust_type = rust_type;
            },
            ParseState::PositionPattern(pos@PositionTypes::Mandatroy | pos@PositionTypes::Optional) => {
                // Parse the pattern for matching argument positions.
                let position_pattern = match token {
                    TokenTree::Group(group) => group.stream(),
                    t => {
                        let span: proc_macro::Span = t.span().unwrap();
                        Diagnostic::spanned(span, proc_macro::Level::Error, "expected a paranthesised pattern matching the argument position here.").emit();
                        panic!("expected a position pattern.");
                    },
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
                    let arg = #arg_pos(arg_type);
                    fn position_matcher<'b>(pattern: &Box<dyn crate::parse::macros::ArgMatcher + 'b>) -> bool {
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
                            kind: argument_type.properties.kind.clone(),
                            position_type: pos,
                            rust_type: rust_type.clone(),
                        }),
                        StringOrInt::Int(offset)  => arg_struct.positional.insert(offset, ArgumentProperties {
                            kind: argument_type.properties.kind.clone(),
                            position_type: pos,
                            rust_type: rust_type.clone(),
                        }),
                    };
                }
            },
        };
        // Handle switching back states, and any additional delimiting tokens.
        match parse_state {
            ParseState::PositionPattern(_) => {
                // Finished parsing a pattern, skip the comma delimiting the next rule.
                let token = stream.next();
                // Expecting to find ',' at this point.
                match match token {
                    Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => Ok(()),
                    Some(t) => Err(t.span().unwrap()),
                    None => Ok(()),
                } {
                    Ok(()) => {},
                    Err(span) => {
                        Diagnostic::spanned(span, proc_macro::Level::Error,
                            "Expected a comma after defining an argument rule.").emit();
                        panic!("expected a comma");
                    }
                };
                // Otherwise, switch back to trying tp parse a new rule.
                parse_state = ParseState::ArgumentPosition;
            },
            _ => {},
        };
    }

    // Build tuple type for arguments structure.
    let tuple_len = *arg_struct.positional.keys().max().unwrap_or(&0);
    let mut tuple_types = vec![quote! { () }; tuple_len + 1];
    for i in 1..=tuple_len {
        let props = arg_struct.positional.get(&i);
        tuple_types[i] = match props {
            Some(props) => props.rust_type.clone(),
            None        => quote! { () },
        };
    }
    // Build named arguments struct fields.
    let mut named_arguments: Vec<TokenStream> = vec![];
    let mut named_types: Vec<TokenStream> = vec![];
    let mut named_values: Vec<TokenStream> = vec![];
    for (name, props) in arg_struct.named.iter() {
        let rust_type = props.rust_type.clone();
        let variable: proc_macro2::TokenStream = format!("r#{}", name).parse().unwrap();
        named_types.push(rust_type);
        named_arguments.push(variable);
        match props.position_type {
            PositionTypes::Mandatroy => named_values.push(quote! {{
                let retrieved = *parser.get(#name)?;
                retrieved
                    .clone()
                    .try_into()
                    .expect("node type-checked but unwrap failed")
            }}),
            PositionTypes::Optional => named_values.push(quote! {{
                parser.get_optional(#name).map(|retrieved|
                    (*retrieved)
                        .clone()
                        .try_into()
                        .expect("node type-checked but unwrap failed"))
            }}),
            _ => unreachable!(),
        }
    }

    // Generate code for extracting the values of the positional arguments.
    let mut tuple_variables = vec![quote! { () }];
    let mut tuple_variable_initializations = vec![];
    for i in 1..=tuple_len {
        let arg_num_name: TokenStream = format!("arg_num_{}", i).parse().unwrap();
        let arg_type = tuple_types[i].clone();

        tuple_variables.push(arg_num_name.clone());
        let Some(props) = arg_struct.positional.get(&i) else { continue };
        match props.position_type {
            PositionTypes::Mandatroy => {
                tuple_variable_initializations.push(quote! {
                    let #arg_num_name: #arg_type = {
                        let retrieved = *parser.get(#i)?;
                        retrieved
                            .clone()
                            .try_into()
                            .expect("node type-checked but unwrap failed")
                    };
                });
            },
            PositionTypes::Optional => {
                tuple_variable_initializations.push(quote! {
                    let #arg_num_name: #arg_type = parser
                        .get_optional(#i)
                        .map(|retrieved|
                            (*retrieved)
                                .clone()
                                .try_into()
                                .expect("node type-checked but unwrap failed"));
                });
            },
            _ => unreachable!(),
        }
    }

    // Generate code for extracting the trailing arguments.
    let rest_rust_type = arg_struct.rest.rust_type;
    let has_rest_capture = arg_struct.rest.kind != ArgumentKind::None;
    let trailing_arguments = if has_rest_capture {
        quote! {
            {
                parser.trailing
                    .iter()
                    .map(|arg| {
                        let arg: crate::parse::parser::ParseNode = (*arg).clone();
                        let retrieved: #rest_rust_type = arg.try_into().expect("node type-checked but unwrap failed");
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
    quote! {
        {
            #(#out)*;
            #[allow(non_camel_case_types)]
            #[derive(Clone, Debug)]
            struct #struct_name<'a> {
                number: (#(#tuple_types),*,),
                #(#named_arguments: #named_types,)*
                #rest_struct_decl
            }
            let parser_result = crate::parse::macros::ArgParser::new(rules, &node, #params);
            match parser_result {
                Ok(parser) => {
                    #(#tuple_variable_initializations)*
                    #(let #named_arguments: #named_types = #named_values;)*
                    let rest = #trailing_arguments;
                    let args_struct = #struct_name {
                        number: (#(#tuple_variables),*,),
                        #(#named_arguments,)*
                        rest,
                    };
                    Ok((parser, args_struct))  // Returns the parser and args from the scope.
                },
                Err(e) => Err(e),
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
            "list" => (AK::List, quote! { Vec<crate::parse::parser::ParseNode<'a>> }, quote! { crate::parse::macros::ArgType::List }),
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
                // TODO: generate predicates based on syntax: "exact", /match/.
                let predicates = group.map(|predicate| match predicate {
                    TokenTree::Literal(literal) => quote! {
                        crate::parse::macros::ArgPredicate::Exactly(String::from(#literal))
                    },
                    token => token.into_token_stream(),
                });
                quote! { #arg_type(vec![ #(#predicates)* ]) }
            },
            _ => panic!("Unexpected list delimiter"),
        },
        // Parse a function which matches the argument.
        Some(TokenTree::Ident(ident)) if ident.to_string() == "fn" => {
            stream.next(); // Consume the `fn` keyword.
            // Consume the function argument list.
            let fn_arguments = match stream.next() {
                Some(TokenTree::Group(group)) => group.stream().into_iter(),
                None => panic!("Unexpected EOF"),
                _ => panic!("Unexpected token"),
            };
            // Consume the function body.
            let Some(fn_body) = stream.next() else { panic!("Unexpected EOF") };
            quote! {{
                fn predicate<'tree>(#(#fn_arguments),*) -> Result<(), ExpansionError<'tree>> { #fn_body }
                let arg_pred = crate::parse::macros::ArgPredicate::Satisfying(predicate);
                #arg_type(vec![arg_pred])
            }}
        }
        _ => quote! { #arg_type(vec![]) },
        //_ => panic!("Unexpected tokens after argument type rules.")
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
