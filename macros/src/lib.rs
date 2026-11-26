//! Procedural macros re-exported by `tsum`. Do not use these macros directly.
#![allow(unused_features)]
#![feature(non_exhaustive_omitted_patterns_lint, proc_macro_expand)]

use proc_macro::TokenStream;
use syn::{Meta, Token, punctuated::Punctuated};

mod id;
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

#[doc(hidden)]
#[proc_macro]
pub fn gen_id(input: TokenStream) -> TokenStream {
    let prefix = syn::parse_macro_input!(input as syn::Path);
    id::element_id(quote::quote!(#prefix), "", proc_macro::Span::call_site()).into()
}

#[proc_macro_derive(Element, attributes(tsum))]
pub fn derive_element(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);

    let mut prefix = quote::quote!(::tsum);

    if let Some(a) = input.attrs.iter().find(|a| a.path().is_ident("tsum")) {
        let nested = match a.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated) {
            Ok(nested) => nested,
            Err(e) => return e.to_compile_error().into(),
        };
        for meta in nested {
            match meta {
                Meta::NameValue(nv) if nv.path.is_ident("crate") => {
                    let value = nv.value;
                    prefix = quote::quote!(#value);
                }
                _ => {
                    return syn::Error::new_spanned(meta, "undefined attribute")
                        .to_compile_error()
                        .into();
                }
            }
        }
    }

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let name = input.ident;
    let id = id::element_id(
        syn::parse_quote!(#prefix::exports::typenum),
        &name.to_string(),
        name.span().unwrap(),
    );
    let expanded = quote::quote! {
        unsafe impl #impl_generics #prefix::union::Element
            for #name #ty_generics #where_clause
        {
            type Id = #id;
        }
    };
    expanded.into()
}
