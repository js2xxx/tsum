#![feature(non_exhaustive_omitted_patterns_lint)]

use proc_macro::TokenStream;

mod pat;

#[proc_macro]
pub fn match_sum(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as pat::SumMatch);
    pat::expand_match(input, true).into()
}

#[proc_macro]
pub fn match_union(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as pat::SumMatch);
    pat::expand_match(input, false).into()
}
