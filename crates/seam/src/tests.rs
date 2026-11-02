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
    fn test_escaped_newline_line_numbers() {
        // an escaped new line in a symbol only counts as one line.
        let error = expand(String::from("(p a\\\nb)\n(%nope)")).unwrap_err();
        assert!(error.contains("<test>:3:1"), "{}", error);
    }

    #[test]
    fn test_pre_with_expanded_contents() {
        // plain contents are copied from the source as written.
        assert_html_document_eq("(pre  x  <y>\n   z)",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<pre> x  <y>\n   z</pre>\n</body>\n</html>");
        // but expanded contents are written out, rather than the macro call.
        assert_html_document_eq("(pre (%embed \"tests/fixtures/post.md\"))",
            "<!DOCTYPE html>\n<html>\n<head></head>\n<body>\n<pre># Title\n\nWritten by (%author).\n</pre>\n</body>\n</html>");
    }
}
