use super::*;

fn expand<'a>(source: String) -> Result<String, Box<dyn 'a + std::error::Error>>  {
    let expander = tree_builder(Some("<test>"), source);
    let expander = Box::leak(Box::new(expander));
    let tree = expander.expand()?;
    let mut ret = String::new();
    for node in tree {
        ret += &format!("{}", node);
    }
    Ok(ret)
}

fn test_output_eq(input: &str, expect: &str) {
    let source = String::from(input);
    let output  = expand(source).unwrap();
    assert_eq!(output, expect);
}

mod tests {
    use super::*;

    #[test]
    fn test_sort_macro_alphanumeric() {
        test_output_eq(
            "(%sort (13 d 8 e 14 f 9 10 g 11 12 a b c 0 0.1 1.5 0.2 1 2 -1 -10 -2 -1.4 -0.3) :order ascending)",
            "(-10 -2 -1.4 -1 -0.3 0 0.1 0.2 1 1.5 2 8 9 10 11 12 13 14 a b c d e f g)"
        );
    }

    #[test]
    fn test_sort_macro_key() {
        // sort by the second element in 3-tuples.
        test_output_eq(
            "(%sort :key (%lambda ((x y z)) %y) ((x 3 b) (z 1 a) (y 2 c)))",
            "((z 1 a) (y 2 c) (x 3 b))"
        );
    }

    #[test]
    fn test_reverse_macro() {
        test_output_eq(
            "(%reverse (a 3  2 1 2 s))",
            "(s 2  1 2 3 a)"
        );
    }
}
