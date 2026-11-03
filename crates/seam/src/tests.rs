use super::*;
use std::fmt::Write;

fn expand(source: String) -> Result<String, String>  {
    let context = Context::new();
    let expander = tree_builder(&context, Some("<test>"), source, false);
    let tree = match expander.expand() {
        Ok(tree) => tree,
        Err(err) => return Err(format!("{err}")),
    };
    let mut out = String::new();
    for node in tree {
        write!(out, "{node}").unwrap();
    }
    Ok(out)
}

/// Expand the source and render it as a complete HTML document.
fn html_document(source: &str) -> Result<String, String> {
    use assemble::MarkupFormatter;
    let context = Context::new();
    let expander = tree_builder(&context, Some("<test>"), source.to_owned(), false);
    let tree = expander.expand().map_err(|err| format!("{err}"))?;
    assemble::html::HTMLFormatter::new(tree).document().map_err(|err| err.message)
}

/// Expand literate source and render it as an HTML fragment.
fn literate_html(source: &str) -> Result<String, String> {
    use assemble::MarkupFormatter;
    let context = Context::new();
    let expander = tree_builder(&context, Some("<test>"), source.to_owned(), true);
    let tree = expander.expand().map_err(|err| format!("{err}"))?;
    assemble::html::HTMLFormatter::new(tree).display().map_err(|err| err.message)
}

/// Expand source and render it as CSS.
fn css(source: &str) -> Result<String, String> {
    use assemble::MarkupFormatter;
    let context = Context::new();
    let expander = tree_builder(&context, Some("<test>"), source.to_owned(), false);
    let tree = expander.expand().map_err(|err| format!("{err}"))?;
    assemble::css::CSSFormatter::new(tree).document().map_err(|err| err.message)
}

fn assert_literate_eq(input: &str, expect: &str) {
    assert_eq!(literate_html(input).as_deref(), Ok(expect));
}

fn assert_html_document_eq(input: &str, expect: &str) {
    assert_eq!(html_document(input).as_deref(), Ok(expect));
}

fn assert_output_eq(input: &str, expect: &str) {
    let source = String::from(input);
    let output = match expand(source) {
        Ok(o) | Err(o) => o,
    };
    assert_eq!(output, expect);
}

mod cases {
    use super::*;

    #[test]
    fn test_sort_macro_alphanumeric() {
        // sort all signed, unsigened, floats and text.
        assert_output_eq(
            "(%sort (13 d 8 e 14 f 9 10 g 11 12 a b c 0 0.1 1.5 0.2 1 2 -1 -10 -2 -1.4 -0.3) :order ascending)",
            "(-10 -2 -1.4 -1 -0.3 0 0.1 0.2 1 1.5 2 8 9 10 11 12 13 14 a b c d e f g)"
        );
    }

    #[test]
    fn test_sort_macro_key() {
        // sort by the second element in 3-tuples.
        assert_output_eq(
            "(%sort :key (%lambda ((x y z)) %y) ((x 3 b) (z 1 a) (y 2 c)))",
            "((z 1 a) (y 2 c) (x 3 b))"
        );
    }

    #[test]
    fn test_reverse_macro() {
        // reverse a list while preserving whitespace-ordering.
        assert_output_eq(
            "(%reverse (a 3  2 1 2 s))",
            "(s 2  1 2 3 a)"
        );
    }

    #[test]
    fn test_date_timestamps() {
        // check %date works with i64 unix timestamps.
        assert_output_eq(
            "(%date \"%Y-%m-%d\" 0)",
            "\"1970-01-01\""
        );
        assert_output_eq(
            "(%date \"%Y-%m-%d %H:%M:%S\" 1733776966)",
            "\"2024-12-09 20:42:46\""
        );
    }

    #[test]
    fn test_date_timezones() {
        assert_output_eq(
            "(%date \"%Y-%m-%d %H:%M:%S%Z\" 999999999 :timezone +1)",
            "\"2001-09-09 02:46:39+01:00\""
        );
        assert_output_eq(
            "(%date \"%Y-%m-%d %H:%M:%S%Z\" 999999999 :timezone +3.5)",
            "\"2001-09-09 05:16:39+03:30\""
        );
        assert_output_eq(
            "(%date \"%Y-%m-%d %H:%M:%S%Z\" 999999999 :timezone -2.25)",
            "\"2001-09-08 23:31:39-02:15\""
        );
    }

    #[test]
    fn test_timestamp_macro() {
        let timestamp = "419083754"; // 13 Apr 1983.
        assert_output_eq(
            "(%timestamp \"%Y %b %d %H:%M:%S%.3f %z\" \"1983 Apr 13 12:09:14.274 +0000\")",
            timestamp
        );
        assert_output_eq(
            "(%timestamp \"%Y %b %d %H:%M:%S%.3f\" \"1983 Apr 13 12:09:14.274\" :timezone 0)",
            timestamp
        );
        // Same time *locally* but in a timezone of -02:00.
        let timestamp_minus_2h = "419090954";
        assert_output_eq(
            "(%timestamp \"%Y %b %d %H:%M:%S%.3f %z\" \"1983 Apr 13 12:09:14.274 -0200\")",
            timestamp_minus_2h
        );
        assert_output_eq(
            "(%timestamp \"%Y %b %d %H:%M:%S%.3f\" \"1983 Apr 13 12:09:14.274\" :timezone -2)",
            timestamp_minus_2h
        );
    }

    #[test]
    fn test_markdown_allow_html() {
        // embedded HTML is passed through by default.
        assert_output_eq(
            "(%markdown \"Hi <b>there</b>\")",
            "\"<p>Hi <b>there</b></p>\""
        );
        // and escaped with `:allow-html false`.
        assert_output_eq(
            "(%markdown :allow-html false \"Hi <b>there</b>\")",
            "\"<p>Hi &lt;b&gt;there&lt;/b&gt;</p>\""
        );
    }

    #[test]
    fn test_lexical_closures() {
        // lambdas keep the scope they were created in.
        assert_output_eq(
            "(%define (adder n) (%lambda (x) %n %x)) (%apply (%adder 1) a) (%apply (%adder 2) b)",
            " 1 a 2 b"
        );
        // each evaluation of the same `%lambda` makes a distinct closure.
        assert_output_eq(
            "(%define fs (%for i in (1 2 3) (%lambda (x) %i %x))) (%for f in (%fs) (%apply %f a))",
            " 1 a 2 a 3 a"
        );
    }

    #[test]
    fn test_lexical_scope_isolation() {
        // a macro does not see its caller's parameters.
        assert_output_eq(
            "(%define x global) (%define (show) %x) (%define (f x) (%show)) (%f local)",
            " global"
        );
        // definitions within a macro body stay local to it.
        assert_output_eq(
            "(%define (outer) (%define (helper) H) (%helper)) (%outer) (%ifdef helper leaked ok)",
            " H ok"
        );
    }

    #[test]
    fn test_namespace_helpers() {
        // namespaced macros use their own helpers, not the caller's.
        assert_output_eq(
            "(%namespace ui (%include \"tests/fixtures/ui.sex\")) (%define sep CALLER) (%ui/nav a b)",
            " a \"|\" b"
        );
    }

    #[test]
    fn test_with_macro() {
        // `%with` overrides top-level definitions for macros called in its body.
        assert_output_eq(
            "(%define title Default) (%define (layout) (t %title)) (%with (:title Cake) (%layout)) (%layout)",
            " (t Cake) (t Default)"
        );
        // but never a macro's own parameters.
        assert_output_eq(
            "(%define title Default) (%define (layout title) (t %title)) (%with (:title Cake) (%layout Param))",
            " (t Param)"
        );
        // innermost bindings win, and they end with the `%with`.
        assert_output_eq(
            "(%define t A) (%with (:t B) (%with (:t C) %t) %t) %t",
            " C B A"
        );
        // bindings may come from collected keyword arguments.
        assert_output_eq(
            "(%define (layout) (t %title %author)) (%define (page &&meta) (%with %meta (%layout))) (%page :title Cake :author Sam)",
            " (t Cake Sam)"
        );
    }

    #[test]
    fn test_include_inside_macro_error() {
        // sources included within a macro call outlive the call,
        // so errors can still show where they came from.
        let output = expand(String::from(
            "(%define (f) (%include \"tests/fixtures/broken.sex\")) (%f)"
        )).unwrap_err();
        assert!(output.contains("tests/fixtures/broken.sex"), "{}", output);
        assert!(output.contains("(p (%undefined-macro))"), "{}", output);
    }

    #[test]
    fn test_html_document_wrapping() {
        // a fragment gets every missing element.
        assert_html_document_eq("(p Hello World)",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<p>Hello World</p>\n</body>\n</html>");
        // loose metadata goes in the head, until the first content.
        assert_html_document_eq("(title T) (p hi) (script \"x()\")",
            "<!DOCTYPE html>\n<html>\n<head>\n<title>T</title>\n</head>\n<body>\n<p>hi</p> <script>\"x()\"</script>\n</body>\n</html>");
        // an explicit head stays a head, rather than ending up in the body.
        assert_html_document_eq("(head (title T)) (p hi)",
            "<!DOCTYPE html>\n<html>\n<head><title>T</title></head>\n<body>\n<p>hi</p>\n</body>\n</html>");
        // an explicit body gets a head before it.
        assert_html_document_eq("(body (p hi))",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body><p>hi</p></body>\n</html>");
        // `html` keeps its attributes, and gets a head and body.
        assert_html_document_eq("(html :lang en (p hi))",
            "<!DOCTYPE html>\n<html lang=\"en\">\n<head></head>\n<body>\n<p>hi</p>\n</body>\n</html>");
        // a doctype alone no longer stops the rest of the document being added.
        assert_html_document_eq("(!doctype html) (p hi)",
            "<!doctype html>\n<html>\n<head></head>\n<body>\n<p>hi</p>\n</body>\n</html>");
        // only the top-level is examined, nested elements are left as written.
        assert_html_document_eq("(div (body x))",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<div><body>x</body></div>\n</body>\n</html>");
    }

    #[test]
    fn test_html_complete_document_unchanged() {
        assert_html_document_eq(
            "(!DOCTYPE html)\n(html :lang en\n  (head (title T))\n  (body (p hi)))",
            "<!DOCTYPE html>\n<html lang=\"en\">\n  <head><title>T</title></head>\n  <body><p>hi</p></body>\n</html>"
        );
    }

    #[test]
    fn test_html_document_errors() {
        let error = |source| html_document(source).unwrap_err();
        assert!(error("(head) (head)").contains("only have one `head'"));
        assert!(error("(body) (body)").contains("only have one `body'"));
        assert!(error("(p hi) (head)").contains("must come before"));
        assert!(error("(html (p)) (p)").contains("outside of the `html'"));
    }

    #[test]
    fn test_literate_mode() {
        // text is kept as written, only `(%...)` calls are parsed.
        assert_literate_eq(
            "hello world (earth) (%do (p letter \"\\x61\")) \"\\x61\"\n",
            "hello world (earth) <p>letter a</p> \"\\x61\"\n"
        );
        // markup and semicolons in text pass straight through.
        assert_literate_eq(
            "<p>a <b>bold</b>; claim</p>",
            "<p>a <b>bold</b>; claim</p>"
        );
        // a macro's result takes the place of the call.
        assert_literate_eq("(%define name Sam)Hi (%name).", "Hi Sam.");
        // `\(%` gives a literal `(%`.
        assert_literate_eq("50\\(%) off", "50(%) off");
        // an unclosed call is an error.
        assert!(literate_html("oops (%do (p x)").unwrap_err().contains("Expected `)'"));
    }

    #[test]
    fn test_literate_include_embed() {
        assert_output_eq(
            "(%define (author) Sam) (%include :literate true \"tests/fixtures/note.txt\")",
            " \"Dear \"Sam\"; (see \"(em this)\")\\n\""
        );
        // without `:literate`, `%embed` gives the file's contents as a string.
        assert_output_eq(
            "(%embed \"tests/fixtures/note.txt\")",
            "\"Dear (%author); (see (%do (em this)))\\n\""
        );
    }

    #[test]
    fn test_literate_markdown() {
        // markdown is literate by default.
        assert_output_eq(
            "(%define (author) Sam) (%markdown (%embed \"tests/fixtures/post.md\"))",
            " \"<h1>Title</h1>\\n<p>Written by Sam.</p>\\n\""
        );
        assert_output_eq(
            "(%markdown :literate false (%embed \"tests/fixtures/post.md\"))",
            "\"<h1>Title</h1>\\n<p>Written by (%author).</p>\\n\""
        );
    }

    #[test]
    fn test_literate_markdown_frontmatter() {
        // only the part being used is expanded.
        let error = expand(String::from(
            "(%markdown :only content (%embed \"tests/fixtures/front-errors.md\"))")).unwrap_err();
        assert!(error.contains("nope-body") && error.contains(":4:"), "{}", error);
        let error = expand(String::from(
            "(%markdown :only frontmatter (%embed \"tests/fixtures/front-errors.md\"))")).unwrap_err();
        assert!(error.contains("nope-front") && error.contains(":2:"), "{}", error);
        // the content can use the frontmatter's definitions.
        assert_output_eq(
            "(%define name Sam) (%markdown (%embed \"tests/fixtures/front.md\"))",
            " \"<h1>Hello Sam</h1>\\n\""
        );
    }

    #[test]
    fn test_format_lists() {
        // lists are formatted as s-expressions.
        assert_output_eq(
            "(%format \"{} and {x}\" (a \"b\" (c)) :x (d))",
            "\"(a \\\"b\\\" (c)) and (d)\""
        );
    }

    #[test]
    fn test_css_selector_functions() {
        assert_eq!(css("(ul li(:nth-child (+ 2n 1)) a :color red)").as_deref(),
            Ok("ul li:nth-child(2n + 1) a {\n  color: red;\n}"));
        // apart from the preceding selector, it selects descendants.
        assert_eq!(css("(p (:not .x) :margin 0)").as_deref(),
            Ok("p :not(.x) {\n  margin: 0;\n}"));
    }

    #[test]
    fn test_arguments_schema() {
        use crate::parse::{expander::ExpansionError, lexer::Lexer, parser::{ParseNode, Parser}};
        use seam_argparse_proc_macro::arguments;
        fn describe<'a>(node: &ParseNode<'a>, params: &[ParseNode<'a>]) -> Result<String, ExpansionError<'a>> {
            let args = arguments! { node, params;
                mandatory(1..=2): symbol,
                optional(3): number fn(n: &ParseNode<'t>) {
                    match n.atomic().map(|n| n.value.parse::<u32>()) {
                        Some(Ok(n)) if n % 2 == 0 => Ok(()),
                        _ => Err(ExpansionError::new("Integer must be even.", n.site())),
                    }
                },
                optional("mode"): literal["fast", "slow"],
                rest: any,
            }?;
            Ok(format!("{} {} {:?} {:?} {}",
                args.number.1.value, args.number.2.value,
                args.number.3.map(|n| &n.value), args.mode.map(|n| &n.value),
                args.rest.len()))
        }
        let check = |source: &str| {
            let parser = Parser::new(Lexer::new("<test>".into(), source.into()));
            let tree = parser.parse().unwrap();
            describe(&tree[0], &tree).map_err(|error| error.0)
        };
        assert_eq!(check("a b").as_deref(), Ok("a b None None 0"));
        assert_eq!(check("a b 4 :mode fast x :y z").as_deref(), Ok("a b Some(\"4\") Some(\"fast\") 2"));
        assert_eq!(check("a"), Err("Missing argument in position 2.".to_owned()));
        assert_eq!(check("a b 3"), Err("Integer must be even.".to_owned()));
        assert_eq!(check("a 1"), Err("Expected a symbol node, got a number instead.".to_owned()));
        assert_eq!(check("a b :mode quick"), Err("This argument's value must be one of: `fast', `slow'.".to_owned()));
        assert_eq!(check("a b :mode fast :mode slow"), Err("Named argument `:mode' is given more than once.".to_owned()));
    }

    /// Expand source to s-expressions.
    fn sexp(source: &str) -> Result<String, String> {
        use assemble::MarkupFormatter;
        let context = Context::new();
        let expander = tree_builder(&context, Some("<test>"), source.to_owned(), false);
        let tree = expander.expand().map_err(|err| format!("{err}"))?;
        assemble::sexp::SExpFormatter::new(tree).document().map_err(|err| err.message)
    }

    fn assert_sexp_eq(input: &str, expect: &str) {
        assert_eq!(sexp(input).as_deref(), Ok(expect), "{input}");
    }

    #[test]
    fn test_math() {
        assert_sexp_eq("(%+ 1 2 3) (%- 10 4 1) (%- 5) (%* 2 3.5) (%/ 6 3) (%/ 7 2)", "6 5 -5 7 2 3.5");
        assert_sexp_eq("(%mod -7 3) (%pow 2 10) (%min 3 1 2) (%max 3 1 2) (%+ 0x10 1)", "2 1024 1 3 17");
        assert_sexp_eq("(%sqrt 16) (%hypot 3 4) (%abs -3) (%floor 2.7) (%round 2.5) (%log10 1000)", "4 5 3 2 3 3");
        assert!(sexp("(%/ 1 0)").unwrap_err().contains("Division by zero"));
        assert!(sexp("(%+ 1 a)").unwrap_err().contains("expects numbers"));
    }

    #[test]
    fn test_logic() {
        assert_sexp_eq("(%= 1 1.0) (%< 1 2 3) (%< 1 3 2) (%= a a) (%!= a b) (%>= 3 3)",
            "true true false true true true");
        // `%if`, `%and` and `%or` only expand what they need.
        assert_sexp_eq("(%if (%< 1 2) yes (%error no)) (%if false (%error yes) no) (%if \"\" yes)", "yes no");
        assert_sexp_eq("(%not ()) (%and a b c) (%and a false (%error x)) (%or false () x (%error y))",
            "true c false x");
    }

    #[test]
    fn test_list_macros() {
        assert_sexp_eq("(%take 2 (a b c d)) (%drop 2 (a b c d)) (%range 1 4) (%range 5 1 -2)",
            "(a b) (c d) (1 2 3 4) (5 3 1)");
        assert_sexp_eq("(%get -1 (a b c)) (%get (1 3) (a b c d e)) (%get (-2 -1) (a b c d e))",
            "c (b c d) (d e)");
        assert_sexp_eq("(%split , \"a,b\") (%split | (a b | c)) (%intercalate , (a b c)) (%length (a b)) (%length héllo)",
            "(\"a\" \"b\") ((a b) (c)) a , b , c 2 5");
        assert_sexp_eq("(%while (%lambda (x) (%< %x 3)) (1 2 3 1))", "(1 2)");
    }

    #[test]
    fn test_dictionary_macros() {
        assert_sexp_eq("(%define d (:a 1 :b 2)) (%items %d) (%keys %d) (%values %d)",
            " ((a 1) (b 2)) (a b) (1 2)");
        // `%for` iterates over what its list expression expands to.
        assert_sexp_eq("(%define d (:a 1 :b 2)) (%for (k v) in (%items %d) %k = %v ,)",
            " a = 1 , b = 2 ,");
    }

    #[test]
    fn test_path_macros() {
        assert_sexp_eq("(%basename :suffix txt /a/f.txt) (%basename /a/f.txt) (%dirname /a/f.txt) (%dirname f) (%extension /a/f.txt)",
            "f f.txt /a . txt");
        assert_sexp_eq("(%path/basename a/b.md) (%path/stem a/b.tar.gz) (%path/with-extension a/b.md html) (%path/join a b/c d.txt)",
            "b.md b.tar \"a/b.html\" \"a/b/c/d.txt\"");
        assert_sexp_eq("(%path/split /a/b.md) (%path/normalise a/./b/../../../c) (%path/normalise /../a)",
            "(\"/\" \"a\" \"b.md\") ../c /a");
        assert_sexp_eq("(%path/absolute :from /a/b ../c) (%path/relative /a/b/c :from /a/d) (%path/relative /a :from /a)",
            "\"/a/c\" \"../b/c\" \".\"");
        assert_sexp_eq("(%path/exists Cargo.toml) (%path/is-file src) (%path/is-directory src) (%path/exists nowhere)",
            "true false true false");
        let cwd = std::env::current_dir().unwrap();
        assert_sexp_eq("(%path/cwd) (%path/relative (%path/cwd))", &format!("\"{}\" \".\"", cwd.display()));
        // Paths of the file a call is written in, which a string of source is not.
        assert_sexp_eq("(%include \"tests/fixtures/here.sex\")",
            &format!("\"{0}/tests/fixtures/here.sex\" \"{0}/tests/fixtures\"", cwd.display()));
        assert!(sexp("(%path/here)").is_err());
        assert_sexp_eq("(%path/this-directory)", &format!("\"{}\"", cwd.display()));
    }

    #[test]
    fn test_error_and_try() {
        assert_eq!(sexp("(%error Something (%+ 1 1) went wrong)").unwrap_err().lines().last(),
            Some("[**] Error Expanding Macro (<test>:1:1): Something 2 went wrong"));
        assert_sexp_eq("(%try (%error bad) :error e caught %e) (%try fine (%error never))", "caught \"bad\" fine");
    }

    #[test]
    fn test_let_quote_eval() {
        assert_sexp_eq("(%let ((a 1) (b (%+ %a 1)) ((c d) (x y))) %a %b %c %d)", "1 2 x y");
        assert_sexp_eq("(%define code (%quote (%+ 1 2))) %code (%eval %code)", " (%+ 1 2) 3");
    }

    #[test]
    fn test_lazy_parameters() {
        // lazy arguments are only expanded when used, in the caller's scope.
        assert_sexp_eq("(%define (unless c ~body) (%if %c () %body)) (%unless true (%error x)) (%unless false ran)",
            " () ran");
        assert_sexp_eq("(%define (my-if c ~a ~b) (%if %c %a %b)) (%define (f x) (%my-if true %x no)) (%f inner)",
            " inner");
        assert_sexp_eq("(%define (twice ~&body) %body %body) (%twice a b)", " a b a b");
        // recursion terminates, since `%if` is lazy.
        assert_sexp_eq("(%define (fact n) (%if (%<= %n 1) 1 (%* %n (%fact (%- %n 1))))) (%fact 10)", " 3628800");
    }

    #[test]
    fn test_typed_parameters() {
        assert_sexp_eq("(%define (r n:number &s:string) %n %s) (%r 2 \"a\" \"b\")", " 2 \"a\" \"b\"");
        assert_sexp_eq("(%define (g :name:string \"you\") %name) (%g) (%g :name \"Sam\")", " \"you\" \"Sam\"");
        assert!(sexp("(%define (r n:number) %n) (%r a)").unwrap_err()
            .contains("Argument `n' of `%r' must be a number, got a symbol instead."));
        assert!(sexp("(%define (r &xs:number) ok) (%r 1 a)").unwrap_err().contains("`xs'"));
        assert!(sexp("(%define (g :n:number x) %n)").unwrap_err().contains("Default value of `:n'"));
    }

    #[test]
    fn test_shell_expansion() {
        let define = "(%define name \"Samuel Knutsen\") (%define file posts/2024-01-hi.md)";
        let check = |expression: &str, expect: &str| assert_sexp_eq(&format!("{define} {expression}"), &format!(" {expect}"));
        check("%{#name} %{name:0:6} %{name:0-7} %{name:7:3}", "14 \"Samuel\" \"Knutsen\" \"Knu\"");
        check("%{file#*/} %{file##*-} %{file%.md} %{file%%-*}", "2024-01-hi.md hi.md posts/2024-01-hi posts/2024");
        check("%{name/Samuel/Sam} %{file//-/_} %{file/#posts/drafts} %{file/%md/html}",
            "\"Sam Knutsen\" posts/2024_01_hi.md drafts/2024-01-hi.md posts/2024-01-hi.html");
        check("%{name^^} %{name,,} %{missing:-none} %{name:+set}",
            "\"SAMUEL KNUTSEN\" \"samuel knutsen\" \"none\" \"set\"");
        assert!(sexp("%{nope}").unwrap_err().contains("No such variable, `nope`."));
    }

    #[test]
    fn test_formatter_macros() {
        assert_html_document_eq("(div (%formatter/sexp (p hi)) (%formatter/html (b <x>)))",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<div>(p hi) <b>&lt;x&gt;</b></div>\n</body>\n</html>");
        assert_eq!(literate_html("(%formatter/css (a :color red))").as_deref(), Ok("a {\n  color: red;\n}"));
    }

    #[test]
    fn test_attribute_lists() {
        assert_eq!(literate_html("(%do (p :style (:color red :margin (0 auto)) :class (a b) x))").as_deref(),
            Ok("<p style=\"color: red; margin: 0 auto;\" class=\"a b\">x</p>"));
    }

    #[test]
    fn test_write_macro() {
        let directory = std::env::temp_dir().join(format!("seam-test-{}", std::process::id()));
        let path = directory.join("nested/out.txt");
        assert_sexp_eq(&format!("(%write {:?} Hello (%+ 1 1))", path.display().to_string()), "");
        assert_eq!(std::fs::read_to_string(&path).ok().as_deref(), Some("Hello 2"));
        let _ = std::fs::remove_dir_all(directory);
    }

    #[cfg(unix)]
    #[test]
    fn test_exec_macro() {
        assert_sexp_eq("(%exec echo hi there) (%exec tr a-z A-Z :stdin shout)", "\"hi there\" \"SHOUT\"");
        assert!(sexp("(%exec false)").unwrap_err().contains("`%exec false' failed"));
    }

    #[test]
    fn test_relative_include() {
        // a file's includes are found relative to it first.
        assert_sexp_eq("(%include \"tests/fixtures/nested/outer.sex\")", "(found inner)");
    }

    #[test]
    fn test_markdown_code_is_not_expanded() {
        assert_output_eq("(%markdown :only content (%embed \"tests/fixtures/code.md\"))",
            "\"<p>Text 2, <code>(%+ 1 1)</code> and:</p>\\n<pre><code>(%+ 1 1)\\n</code></pre>\\n\"");
    }

    #[test]
    fn test_unique_contains_and_dates() {
        assert_sexp_eq("(%unique (a b a c b)) (%contains b (a b)) (%contains z (a b)) (%if \"false\" y n)",
            "(a b c) true false n");
        assert_sexp_eq("(%timestamp \"%Y-%m-%d\" 2024-03-10 :timezone 0)", "1710028800");
    }

    #[test]
    fn test_escaped_newline_line_numbers() {
        // an escaped new line in a symbol only counts as one line.
        let error = expand(String::from("(p a\\\nb)\n(%nope)")).unwrap_err();
        assert!(error.contains("<test>:3:1"), "{}", error);
    }

    #[test]
    fn test_pre_with_expanded_contents() {
        // plain contents are copied from the source as written.
        assert_html_document_eq("(pre  x  <y>\n   z)",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<pre> x  &lt;y&gt;\n   z</pre>\n</body>\n</html>");
        // but expanded contents are written out, rather than the macro call.
        assert_html_document_eq("(pre (%embed \"tests/fixtures/post.md\"))",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<pre># Title\n\nWritten by (%author).\n</pre>\n</body>\n</html>");
    }

    #[test]
    fn test_pre_verbatim_and_expanded() {
        let pre = |source: &str| {
            use assemble::MarkupFormatter;
            let context = Context::new();
            let expander = tree_builder(&context, Some("<test>"), source.to_owned(), false);
            assemble::html::HTMLFormatter::new(expander.expand().unwrap()).display().unwrap()
        };
        // source text is kept exactly, including comments, but escaped.
        assert_eq!(pre("(pre (f x) ; note\n  (* x  x))"), "<pre>(f x) ; note\n  (* x  x)</pre>");
        assert_eq!(pre("(pre a < b)"), "<pre>a &lt; b</pre>");
        // variables and macros are expanded, rather than shown as written.
        assert_eq!(pre("(%define name Sam) (pre Hi %name)"), " <pre>Hi Sam</pre>");
        assert_eq!(pre("(pre (%do x) y)"), "<pre>x y</pre>");
        // the text of `title` and `textarea` is escaped too.
        assert_eq!(pre("(textarea </textarea>)"), "<textarea>&lt;/textarea&gt;</textarea>");
    }

    #[test]
    fn test_attribute_values_escaped() {
        // a value cannot close its quotes and add attributes, e.g. event handlers.
        assert_html_document_eq("(p :x \"a\\\" onclick=\\\"f()\" y)",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<p x=\"a&quot; onclick=&quot;f()\">y</p>\n</body>\n</html>");
    }
}
