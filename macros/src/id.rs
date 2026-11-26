use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

use proc_macro2::TokenStream;
use quote::quote;

pub(crate) fn element_id(prefix: TokenStream, name: &str, span: proc_macro::Span) -> TokenStream {
    // A compiler process can expand derives for just one of several crates
    // whose elements will eventually appear together. Include the definition
    // site so their keys do not depend on a process-local expansion counter.
    let mut hash = DefaultHasher::new();
    std::env::var_os("CARGO_PKG_NAME").hash(&mut hash);
    std::env::var_os("CARGO_PKG_VERSION").hash(&mut hash);
    std::env::var_os("CARGO_CRATE_NAME").hash(&mut hash);
    (name, span.file(), span.line(), span.column()).hash(&mut hash);
    // Macro-generated definitions can share every source coordinate while
    // belonging to different modules. Resolve the module at the derive site.
    let module: proc_macro::TokenStream = quote!(::core::module_path!()).into();
    module
        .expand_expr()
        .expect("module_path! expands to a literal")
        .to_string()
        .hash(&mut hash);
    let bits = hash.finish();

    // The leading one separates derived IDs from the small primitive IDs.
    // Append bits most significant first to construct a canonical typenum.
    let mut id = quote!(#prefix::uint::UInt<#prefix::uint::UTerm, #prefix::bit::B1>);
    for shift in (0..63).rev() {
        let bit = if bits >> shift & 1 == 0 {
            quote!(#prefix::bit::B0)
        } else {
            quote!(#prefix::bit::B1)
        };
        id = quote!(#prefix::uint::UInt<#id, #bit>);
    }
    id
}
