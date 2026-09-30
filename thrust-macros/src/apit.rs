//! Desugaring of argument-position `impl Trait` (APIT) into named generic parameters.
//!
//! The generated companions (`#[thrust::formula_fn]` and the extern-spec wrapper)
//! spell every parameter type out inside a qualified path
//! (`<T as thrust_models::Model>::Ty`), where rustc rejects `impl Trait`
//! (`error[E0562]`). Rewriting each `impl Bound` occurring in a parameter type into a
//! fresh `__ThrustApitN: Bound` type parameter — mirroring what rustc itself does
//! for the annotated function — lets those companions be written at all.

use proc_macro::TokenStream;
use proc_macro2::{Ident, TokenStream as TokenStream2};
use quote::{format_ident, quote};
use syn::{parse::Parser as _, punctuated::Punctuated, visit_mut::VisitMut as _, Token};

const PARAM_PREFIX: &str = "__ThrustApit";

/// The number of argument-position `impl Trait` occurrences in the parameter types of `sig`.
pub fn count_arg_position_impl_traits(sig: &syn::Signature) -> usize {
    struct Visitor {
        count: usize,
    }
    impl syn::visit::Visit<'_> for Visitor {
        fn visit_type_impl_trait(&mut self, _: &syn::TypeImplTrait) {
            self.count += 1;
        }
    }
    let mut visitor = Visitor { count: 0 };
    for arg in &sig.inputs {
        syn::visit::Visit::visit_fn_arg(&mut visitor, arg);
    }
    visitor.count
}

/// Expands `#[thrust_macros::impl_trait_names(D, F)]`: checks the names against the
/// function and records them for the specification macros, which use them in place of
/// the generated `__ThrustApitN` parameter names.
pub fn expand_names(attr: TokenStream, item: TokenStream) -> TokenStream {
    let item = TokenStream2::from(item);
    match record_names(attr.into(), &item) {
        Ok(marker) => quote!(#marker #item),
        Err(e) => {
            let e = e.to_compile_error();
            quote!(#e #item)
        }
    }
    .into()
}

fn record_names(attr: TokenStream2, item: &TokenStream2) -> syn::Result<syn::Attribute> {
    let names = Punctuated::<Ident, Token![,]>::parse_terminated.parse2(attr.clone())?;
    let func: crate::spec::FnItemWithSignature = syn::parse2(item.clone())?;
    let sig = func.sig();
    let count = count_arg_position_impl_traits(sig);
    if names.len() != count {
        return Err(syn::Error::new_spanned(
            &attr,
            format!(
                "`{}` has {count} argument-position `impl Trait` parameter(s) but {} name(s) are given",
                sig.ident,
                names.len()
            ),
        ));
    }
    let own: Vec<&Ident> = sig
        .generics
        .params
        .iter()
        .filter_map(|param| match param {
            syn::GenericParam::Type(param) => Some(&param.ident),
            syn::GenericParam::Const(param) => Some(&param.ident),
            syn::GenericParam::Lifetime(_) => None,
        })
        .collect();
    for (i, name) in names.iter().enumerate() {
        if own.contains(&name) || names.iter().take(i).any(|earlier| earlier == name) {
            return Err(syn::Error::new_spanned(
                name,
                format!("`{name}` is already a generic parameter of `{}`", sig.ident),
            ));
        }
    }
    let names = names.iter();
    Ok(syn::parse_quote!(#[thrust::_impl_trait_names(#(#names),*)]))
}

/// Removes the marker recorded by [`expand_names`] from `attrs` and returns its names.
pub fn take_names(attrs: &mut Vec<syn::Attribute>) -> Vec<Ident> {
    let marker: syn::Path = syn::parse_quote!(thrust::_impl_trait_names);
    let names = attrs
        .iter()
        .find(|attr| attr.path() == &marker)
        .map(|attr| {
            attr.parse_args_with(Punctuated::<Ident, Token![,]>::parse_terminated)
                .into_iter()
                .flatten()
                .collect()
        });
    attrs.retain(|attr| attr.path() != &marker);
    names.unwrap_or_default()
}

/// Rewrites every argument-position `impl Trait` of `sig` — including nested ones such
/// as the one in `&Wrapper<impl Tr>` — into a fresh type parameter `__ThrustApitN`
/// carrying its bounds (named by the Nth of `names` when given), appended to the signature's generics in order of occurrence.
///
/// The appended order matches rustc's own desugaring of the annotated function, whose
/// synthetic parameters likewise follow the written ones, so a companion built from the
/// returned signature can be instantiated with the annotated function's generic
/// arguments positionally (see `analyze::Analyzer::formula_fn_with_args`).
///
/// Returns a clone of `sig` when it has no argument-position `impl Trait`, which makes
/// the rewrite idempotent.
pub fn desugar_signature(sig: &syn::Signature, names: &[Ident]) -> syn::Signature {
    struct Visitor<'a> {
        names: &'a [Ident],
        params: Vec<syn::TypeParam>,
    }

    impl syn::visit_mut::VisitMut for Visitor<'_> {
        fn visit_type_mut(&mut self, ty: &mut syn::Type) {
            let syn::Type::ImplTrait(impl_trait) = ty else {
                syn::visit_mut::visit_type_mut(self, ty);
                return;
            };
            let n = self.params.len();
            let ident = self
                .names
                .get(n)
                .cloned()
                .unwrap_or_else(|| format_ident!("{}{}", PARAM_PREFIX, n));
            let bounds = &impl_trait.bounds;
            self.params.push(syn::parse_quote!(#ident: #bounds));
            *ty = syn::parse_quote!(#ident);
        }
    }

    let mut sig = sig.clone();
    let mut visitor = Visitor {
        names,
        params: Vec::new(),
    };
    for arg in &mut sig.inputs {
        visitor.visit_fn_arg_mut(arg);
    }
    for param in visitor.params {
        sig.generics.params.push(syn::GenericParam::Type(param));
    }
    sig
}
