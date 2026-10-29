use super::*;

fn expand(source: String) -> Result<String, String>  {
    let context = Context::new();
    let expander = tree_builder(&context, Some("<test>"), source);
    let tree = match expander.expand() {
        Ok(tree) => tree,
        Err(err) => return Err(format!("{}", err)),
    };
    let mut out = String::new();
    for node in tree {
        out += &format!("{}", node);
    }
    Ok(out)
}

fn assert_output_eq(input: &str, expect: &str) {
    let source = String::from(input);
    let output = match expand(source) {
        Ok(o) => o,
        Err(o) => o,
    };
    assert_eq!(output, expect);
}

mod tests {
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
}
