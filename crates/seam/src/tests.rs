use super::*;

fn expand(source: String) -> Result<String, String>  {
    let expander = tree_builder(Some("<test>"), source);
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
}
