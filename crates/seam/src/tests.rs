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

mod tests {
    use super::*;

    #[test]
    fn test_sort_macro_alphanumeric() {
        let source = "(%sort (13 d 8 e 14 f 9 10 g 11 12 a b c 0 0.1 1.5 0.2 1 2 -1 -10 -2 -1.4 -0.3) :order ascending)";
        let source = String::from(source);
        let output  = expand(source).unwrap();
        let expect = "(-10 -2 -1.4 -1 -0.3 0 0.1 0.2 1 1.5 2 8 9 10 11 12 13 14 a b c d e f g)";
        assert_eq!(output, expect);
    }

    #[test]
    fn test_sort_macro_key() {
        // sort by the second element in 3-tuples.
        let source = "(%sort :key (%lambda ((x y z)) %y) ((x 3 b) (z 1 a) (y 2 c)))";
        let source = String::from(source);
        let output  = expand(source).unwrap();
        let expect = "((z 1 a) (y 2 c) (x 3 b))";
        assert_eq!(output, expect);
    }
}
