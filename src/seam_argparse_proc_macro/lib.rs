use proc_macro::TokenStream;

#[proc_macro]
pub fn make_answer(stream: TokenStream) -> TokenStream {
    "fn answer() -> u32 { 42 }".parse().unwrap()
}
