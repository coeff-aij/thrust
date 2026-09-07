//! Desugaring of argument-position `impl Trait` (APIT) into named generic parameters.
//!
//! The generated companions (`#[thrust::formula_fn]` and the extern-spec wrapper)
//! spell every parameter type out inside a qualified path
//! (`<T as thrust_models::Model>::Ty`), where rustc rejects `impl Trait`
//! (`error[E0562]`). Rewriting each `impl Bound` occurring in a parameter type into a
//! fresh `__ThrustApitN: Bound` type parameter — mirroring what rustc itself does
//! for the annotated function — lets those companions be written at all.

use quote::format_ident;
use syn::visit_mut::VisitMut as _;

const PARAM_PREFIX: &str = "__ThrustApit";

/// Whether any parameter type of `sig` contains an argument-position `impl Trait`.
pub fn has_arg_position_impl_trait(sig: &syn::Signature) -> bool {
    struct Visitor {
        found: bool,
    }
    impl syn::visit::Visit<'_> for Visitor {
        fn visit_type_impl_trait(&mut self, _: &syn::TypeImplTrait) {
            self.found = true;
        }
    }
    let mut visitor = Visitor { found: false };
    for arg in &sig.inputs {
        syn::visit::Visit::visit_fn_arg(&mut visitor, arg);
    }
    visitor.found
}

/// Rewrites every argument-position `impl Trait` of `sig` — including nested ones such
/// as the one in `&Wrapper<impl Tr>` — into a fresh type parameter `__ThrustApitN`
/// carrying its bounds, appended to the signature's generics in order of occurrence.
///
/// The appended order matches rustc's own desugaring of the annotated function, whose
/// synthetic parameters likewise follow the written ones, so a companion built from the
/// returned signature can be instantiated with the annotated function's generic
/// arguments positionally (see `analyze::Analyzer::formula_fn_with_args`).
///
/// Returns a clone of `sig` when it has no argument-position `impl Trait`, which makes
/// the rewrite idempotent.
pub fn desugar_signature(sig: &syn::Signature) -> syn::Signature {
    struct Visitor {
        params: Vec<syn::TypeParam>,
    }

    impl syn::visit_mut::VisitMut for Visitor {
        fn visit_type_mut(&mut self, ty: &mut syn::Type) {
            let syn::Type::ImplTrait(impl_trait) = ty else {
                syn::visit_mut::visit_type_mut(self, ty);
                return;
            };
            let ident = format_ident!("{}{}", PARAM_PREFIX, self.params.len());
            let bounds = &impl_trait.bounds;
            self.params.push(syn::parse_quote!(#ident: #bounds));
            *ty = syn::parse_quote!(#ident);
        }
    }

    let mut sig = sig.clone();
    let mut visitor = Visitor { params: Vec::new() };
    for arg in &mut sig.inputs {
        visitor.visit_fn_arg_mut(arg);
    }
    for param in visitor.params {
        sig.generics.params.push(syn::GenericParam::Type(param));
    }
    sig
}
