use std::iter;

use const_random::const_random;
use convert_case::{Case, Casing};
use either::Either::{Left, Right};
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote};
use syn::{parse::Parse, spanned::Spanned, visit::Visit, *};

#[derive(Default)]
struct SumPat {
    root_ident: Option<syn::PatIdent>,
    is_wildcard: bool,
    variants: Vec<Type>,
    variant_pats: Vec<Pat>,
    is_non_exhaustive: bool,

    is_in_subpat: bool,
    err: Option<syn::Error>,
}

impl SumPat {
    fn check_ty(&mut self, ty: &Type) -> bool {
        if self.variants.iter().any(|d| d == ty) {
            self.err = Some(syn::Error::new_spanned(
                ty,
                "splitting the same variant type into multiple patterns is not supported",
            ));
            return false;
        }
        true
    }

    fn check_ty_with_other(&self, other: &Self) -> Option<syn::Error> {
        self.variants.iter().find_map(|d| {
            let any = other.variants.iter().any(|e| d == e);
            if any && !self.is_non_exhaustive && !other.is_non_exhaustive {
                return Some(syn::Error::new_spanned(
                    d,
                    "multiple exhaustive patterns on the same variant type are not supported",
                ));
            }
            None
        })
    }

    fn push_ty(&mut self, ty: Type, root_ident: Option<syn::PatIdent>, i: &syn::Pat) {
        self.variants.push(ty);
        self.variant_pats.push(match root_ident {
            Some(mut pi) => {
                pi.subpat = Some((<Token![@]>::default(), Box::new(i.clone())));
                Pat::Ident(pi)
            }
            None => i.clone(),
        });
    }
}

impl Visit<'_> for SumPat {
    fn visit_pat(&mut self, i: &'_ syn::Pat) {
        match i {
            #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
            Pat::Ident(pi) => {
                if !self.is_in_subpat {
                    let s = pi.ident.to_string();
                    if pi.subpat.is_none() && s.is_case(Case::Pascal) {
                        let ty = Type::Path(syn::TypePath {
                            qself: None,
                            path: syn::Path::from(pi.ident.clone()),
                        });

                        if self.check_ty(&ty) {
                            let root_ident = self.root_ident.take();
                            self.push_ty(ty, root_ident, i);
                        }

                        return;
                    }

                    let mut pat_ident = pi.clone();
                    pat_ident.subpat = None;
                    self.root_ident = Some(pat_ident);
                }
                visit::visit_pat(self, i);
            }

            Pat::Struct(syn::PatStruct { qself, path, .. })
            | Pat::TupleStruct(syn::PatTupleStruct { qself, path, .. })
            | Pat::Path(syn::PatPath { qself, path, .. }) => {
                assert!(!self.is_in_subpat);

                let ty = Type::Path(syn::TypePath {
                    qself: qself.clone(),
                    path: path.clone(),
                });

                if self.check_ty(&ty) {
                    let root_ident = self.root_ident.take();

                    self.is_in_subpat = true;
                    visit::visit_pat(self, i);
                    self.is_in_subpat = false;

                    self.push_ty(ty, root_ident, i);
                }
            }

            Pat::Paren(_) => visit::visit_pat(self, i),
            Pat::Or(_) => {
                if !self.is_in_subpat
                    && let Some(pi) = self.root_ident.take()
                {
                    self.err = Some(syn::Error::new_spanned(
                        pi,
                        "root ident bindings on different variant types are not supported",
                    ));
                    return;
                }
                visit::visit_pat(self, i)
            }

            Pat::Lit(lit) if !self.is_in_subpat => {
                self.is_non_exhaustive = true;
                let mut err = None;
                if let Some(ty) = match &lit.lit {
                    Lit::Str(_) => Some(parse_quote!(&str)),
                    Lit::ByteStr(_) => Some(parse_quote!(&[u8])),
                    Lit::CStr(_) => Some(parse_quote!(&::core::ffi::CStr)),
                    Lit::Byte(_) => Some(parse_quote!(u8)),
                    Lit::Char(_) => Some(parse_quote!(char)),
                    Lit::Int(int) => parse_str(int.suffix())
                        .inspect_err(|_| {
                            err = Some(syn::Error::new_spanned(
                                i,
                                "please specify the suffix of the integer literal",
                            ))
                        })
                        .ok(),
                    Lit::Float(float) => parse_str(float.suffix())
                        .inspect_err(|_| {
                            err = Some(syn::Error::new_spanned(
                                i,
                                "please specify the suffix of the float literal",
                            ))
                        })
                        .ok(),
                    Lit::Bool(_) => Some(parse_quote!(bool)),
                    Lit::Verbatim(_) => None,
                    _ => None,
                } {
                    if self.check_ty(&ty) {
                        let root_ident = self.root_ident.take();
                        self.push_ty(ty, root_ident, i);
                    }
                } else {
                    self.err = err.or_else(|| {
                        Some(syn::Error::new_spanned(
                            i,
                            format_args!("pattern {} are not supported", i.to_token_stream()),
                        ))
                    });
                }
            }

            Pat::Wild(_) | Pat::Range(ExprRange { start: None, end: None, .. }) | Pat::Rest(_)
                if !self.is_in_subpat =>
            {
                self.is_wildcard = true;
            }

            Pat::Const(_)
            | Pat::Range(_)
            | Pat::Macro(_)
            | Pat::Reference(_)
            | Pat::Slice(_)
            | Pat::Type(_)
            | Pat::Verbatim(_)
            | Pat::Tuple(_)
                if !self.is_in_subpat =>
            {
                self.err = Some(syn::Error::new_spanned(
                    i,
                    format_args!("pattern {} are not supported", i.to_token_stream()),
                ))
            }

            Pat::Const(_) | Pat::Lit(_) => {
                self.is_non_exhaustive = true;
                visit::visit_pat(self, i)
            }
            Pat::Range(syn::ExprRange { start, end, .. }) if start.is_some() || end.is_some() => {
                self.is_non_exhaustive = true;
                visit::visit_pat(self, i)
            }

            _ => visit::visit_pat(self, i),
        }
    }
}

pub struct SumArm {
    pat: SumPat,
    guard: Option<Box<Expr>>,
    expr: Box<Expr>,
}

impl Parse for SumArm {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let syn::Arm { attrs, pat, guard, body, .. } = input.parse()?;

        if let (Some(first), Some(last)) = (attrs.first(), attrs.last()) {
            return Err(syn::Error::new(
                first.span().join(last.span()).unwrap(),
                "custom attributes are not supported on match arms",
            ));
        }

        let mut branches = SumPat::default();
        branches.visit_pat(&pat);

        if let Some(err) = branches.err.take() {
            return Err(err);
        }

        if branches.variants.is_empty() && !branches.is_wildcard {
            return Err(syn::Error::new(
                Span::call_site(),
                "cannot infer variant types; please specify at least one variant type in the pattern",
            ));
        }

        if guard.is_some() {
            branches.is_non_exhaustive = true;
        }

        Ok(SumArm {
            pat: branches,
            guard: guard.map(|g| g.1),
            expr: body,
        })
    }
}

pub struct SumMatch {
    expr: Box<Expr>,
    attrs: Vec<syn::Attribute>,
    arms: Vec<SumArm>,
}

impl Parse for SumMatch {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let expr = Box::new(Expr::parse_without_eager_brace(input)?);

        let content;
        syn::braced!(content in input);

        let attrs = syn::Attribute::parse_inner(&content)?;

        let mut arms = Vec::new();
        while !content.is_empty() {
            arms.push(content.parse()?);
        }

        Ok(SumMatch { expr, attrs, arms })
    }
}

pub fn expand_body(
    attrs: &[syn::Attribute],
    arms: &mut [SumArm],
    base_ident: &Ident,
    tagged: bool,
) -> TokenStream {
    let root_label = Lifetime::new(
        &format!("'__sum_match_root{}", const_random!(u32)),
        Span::call_site(),
    );
    let body = Lifetime::new(
        &format!("'__sum_match_body{}", const_random!(u32)),
        Span::call_site(),
    );

    let prefix = if tagged {
        quote!(tsum::sum::Sum)
    } else {
        quote!(tsum::union::Union)
    };
    let tagged = tagged.then(|| quote!(, _));

    let branches = arms.iter_mut().flat_map(|arm| {
        let SumArm { pat, guard, expr } = arm;
        let SumPat {
            is_wildcard,
            variants,
            variant_pats,
            is_non_exhaustive,
            ..
        } = pat;

        if *is_wildcard {
            Left(
                [quote! {
                    let #base_ident = match #base_ident.narrow::<() #tagged>() {
                        #[allow(unreachable_code)]
                        Err(_) => {
                            #[warn(unreachable_code)]
                            let ret = #root_label: { #expr };
                            break #body ret;
                        },
                        Ok(unreachable) => unreachable,
                    };
                }]
                .into_iter(),
            )
        } else {
            let iter = (variants.iter().zip(variant_pats)).zip(iter::repeat((&*guard, &*expr)));
            Right(iter.map(|((variant, pat), (guard, expr))| {
                let success = quote! {{
                    #[warn(unreachable_code, clippy::diverging_sub_expression)]
                    let ret = #root_label: { #expr };
                    break #body ret;
                }};
                match guard {
                    Some(guard) => quote! {
                        let mut #base_ident = #base_ident;
                        #base_ident = match #base_ident.try_unwrap::<#variant #tagged>() {
                            #[allow(unreachable_code, clippy::diverging_sub_expression)]
                            Ok(#pat) if #guard => #success,
                            Ok(res) => #prefix::new(res),
                            Err(rem) => rem.broaden(),
                        };
                    },
                    None if *is_non_exhaustive => quote! {
                        let mut #base_ident = #base_ident;
                        #base_ident = match #base_ident.try_unwrap::<#variant #tagged>() {
                            #[allow(unreachable_code, clippy::diverging_sub_expression)]
                            Ok(#pat) => #success,
                            Ok(res) => #prefix::new(res),
                            Err(rem) => rem.broaden(),
                        };
                    },
                    None => quote! {
                        let #base_ident = match #base_ident.try_unwrap::<#variant #tagged>() {
                            #[allow(unreachable_code, clippy::diverging_sub_expression)]
                            Ok(#pat) => #success,
                            Err(rem) => rem,
                        };
                    },
                }
            }))
        }
    });

    let rest = quote! {
        let #base_ident: #prefix<()> = #base_ident;
        #base_ident.unreachable()
    };

    quote! {#body: {
        #(#attrs)*
        #(#branches)*
        #rest
    }}
}

pub fn expand_match(data: SumMatch, tagged: bool) -> TokenStream {
    let SumMatch { expr, attrs, mut arms } = data;
    let base_ident = format_ident!("__sum_match_base{}", const_random!(u32));

    if let Some(err) = (arms.iter().enumerate())
        .flat_map(|(index, a)| arms.iter().take(index).map(move |b| (a, b)))
        .find_map(|(a, b)| a.pat.check_ty_with_other(&b.pat))
    {
        return err.to_compile_error();
    }

    let body = expand_body(&attrs, &mut arms, &base_ident, tagged);
    quote! {{
        let #base_ident = #expr;
        #body
    }}
}
