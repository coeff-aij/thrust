//! Expansion of `#[thrust_macros::context]`.
//!
//! Makes the enclosing context available to the specifications written inside an item.
//!
//! On a function, every `thrust_macros::invariant!(...)` and `thrust_macros::ghost!(...)`
//! in the body is rewritten into its context-carrying counterpart, carrying the host
//! signature and, for a method, the enclosing `impl`/`trait` header, so a formula may
//! refer to generic- and `Self`-typed variables that the standalone macros cannot see.
//! That also extends the function's where clause with the `Model` predicates for every
//! in-scope type parameter (and for `Self` when used), since each injected marker call
//! instantiates a `Model`-bounded formula function with the host's own generics.
//!
//! On an `impl`/`trait`, each method is stamped with the enclosing header — which is what
//! method-level `requires`/`ensures` read to recover the outer generics — and with this
//! attribute, so a method's body is threaded by an expansion of its own.
//!
//! On an `impl Trait for Ty`, the method-level `requires`/`ensures` are additionally
//! moved out to a sibling inherent `impl Ty` as extern-spec wrappers
//! (see [`extern_spec_impl`]), since their expansion cannot live in a trait impl.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens as _};
use syn::{
    parse::{Parse, ParseStream},
    visit_mut::VisitMut,
    Signature,
};

use crate::{fn_outer_item::FnOuterItem, spec::FnItemWithSignature};

pub fn expand(item: TokenStream) -> TokenStream {
    match syn::parse_macro_input!(item as ContextItem) {
        ContextItem::Fn(func) => expand_fn(func),
        ContextItem::Outer(outer_item) => expand_outer(outer_item),
    }
}

/// An item `#[thrust_macros::context]` applies to.
enum ContextItem {
    Fn(FnItemWithSignature),
    Outer(FnOuterItem),
}

impl Parse for ContextItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative as _;

        let fork = input.fork();
        if let Ok(func) = fork.parse::<FnItemWithSignature>() {
            input.advance_to(&fork);
            return Ok(Self::Fn(func));
        }

        input.parse().map(Self::Outer)
    }
}

/// Hands each method the enclosing header, and the attribute that puts it to use.
/// For a trait impl, also emits the sibling impl carrying the methods' specifications.
fn expand_outer(mut outer_item: FnOuterItem) -> TokenStream {
    let extern_specs = match &mut outer_item {
        FnOuterItem::ItemImpl(item_impl) if item_impl.trait_.is_some() => {
            match extern_spec_impl(item_impl) {
                Ok(tokens) => tokens,
                Err(e) => return e.to_compile_error().into(),
            }
        }
        _ => TokenStream2::new(),
    };

    let header = outer_item.clone().into_header_only();
    let method_attrs: [syn::Attribute; 2] = [
        syn::parse_quote!(#[thrust::_outer_context(#header)]),
        syn::parse_quote!(#[::thrust_macros::context]),
    ];
    match &mut outer_item {
        FnOuterItem::ItemImpl(item_impl) => {
            for item in &mut item_impl.items {
                let syn::ImplItem::Fn(item) = item else {
                    continue;
                };
                item.attrs.extend(method_attrs.clone());
            }
        }
        FnOuterItem::ItemTrait(item_trait) => {
            for item in &mut item_trait.items {
                let syn::TraitItem::Fn(item) = item else {
                    continue;
                };
                item.attrs.extend(method_attrs.clone());
            }
        }
    }
    quote! {
        #outer_item
        #extern_specs
    }
    .into()
}

/// Moves the `requires`/`ensures` of each specified method of `impl Trait for Ty` into a
/// sibling inherent `impl Ty`, and returns that impl (empty when no method is specified).
///
/// The expansion of a specification is not a single item: it needs the two
/// `#[thrust::formula_fn]` companions and the `#[thrust::extern_spec_fn]` wrapper that
/// links them to the specified function. Emitted in place, none of the three is a member
/// of the trait (E0407), so instead the wrapper is emitted next to the impl, in an
/// inherent impl of the same self type and generics — where the companions, which name
/// `Self` and the outer generics, still resolve. The wrapper's body is a tail call to the
/// specified method, which is how `#[thrust::extern_spec_fn]` names its target; only the
/// wrapper is skipped from the analysis, so the trait impl's own body is still verified
/// against the specification, and static call sites of the method use it.
fn extern_spec_impl(item_impl: &mut syn::ItemImpl) -> syn::Result<TokenStream2> {
    let Some((trait_path, _)) = &item_impl.trait_ else {
        return Ok(TokenStream2::new());
    };
    let trait_path = trait_path.clone();
    let self_ty = (*item_impl.self_ty).clone();
    // `Self::Assoc` is ill-formed in an inherent impl (E0223), so the wrapper signatures
    // spell out what this impl declares the projection to be.
    let assoc_types: Vec<(syn::Ident, syn::Type)> = item_impl
        .items
        .iter()
        .filter_map(|item| match item {
            syn::ImplItem::Type(ty) if ty.generics.params.is_empty() => {
                Some((ty.ident.clone(), ty.ty.clone()))
            }
            _ => None,
        })
        .collect();

    let trusted_path: syn::Path = syn::parse_quote!(thrust::trusted);
    let mut wrappers = Vec::new();
    for item in &mut item_impl.items {
        let syn::ImplItem::Fn(method) = item else {
            continue;
        };
        let specs = take_spec_attrs(&mut method.attrs);
        if specs.is_empty() {
            continue;
        }
        // A trusted body is not verified against the specification the wrapper now
        // carries, mirroring what an inherent impl's expansion does with the attribute.
        for attr in &mut method.attrs {
            if attr.path() == &trusted_path {
                *attr = syn::parse_quote!(#[thrust::ignored]);
            }
        }
        wrappers.push(extern_spec_wrapper(
            method,
            &specs,
            &self_ty,
            &trait_path,
            &assoc_types,
        )?);
    }
    if wrappers.is_empty() {
        return Ok(TokenStream2::new());
    }

    let (impl_generics, _, where_clause) = item_impl.generics.split_for_impl();
    Ok(quote! {
        #[::thrust_macros::context]
        impl #impl_generics #self_ty #where_clause {
            #(#wrappers)*
        }
    })
}

/// The extern-spec wrapper for one specified method of a trait impl: the method's own
/// signature, under a fresh name and with the `Self::Assoc` projections resolved, over a
/// body that tail-calls the method.
fn extern_spec_wrapper(
    method: &syn::ImplItemFn,
    specs: &[syn::Attribute],
    self_ty: &syn::Type,
    trait_path: &syn::Path,
    assoc_types: &[(syn::Ident, syn::Type)],
) -> syn::Result<TokenStream2> {
    let name = method.sig.ident.clone();
    let turbofish = crate::spec::generic_turbofish(&method.sig.generics);

    let mut sig = method.sig.clone();
    sig.ident = format_ident!("_thrust_extern_spec_{}", name);
    SelfAssocResolver { assoc_types }.visit_signature_mut(&mut sig);

    let mut args = Vec::new();
    for arg in &sig.inputs {
        match arg {
            syn::FnArg::Receiver(_) => args.push(quote!(self)),
            syn::FnArg::Typed(pat_type) => match &*pat_type.pat {
                syn::Pat::Ident(pat_ident) => {
                    let ident = &pat_ident.ident;
                    args.push(quote!(#ident));
                }
                pat => {
                    return Err(syn::Error::new_spanned(
                        pat,
                        "a specified method of a trait impl takes each parameter by name",
                    ))
                }
            },
        }
    }

    Ok(quote! {
        #[thrust::extern_spec_fn]
        #[allow(dead_code)]
        #(#specs)*
        #sig {
            <#self_ty as #trait_path>::#name #turbofish(#(#args),*)
        }
    })
}

/// Takes the specification attributes off a method, keeping their order.
fn take_spec_attrs(attrs: &mut Vec<syn::Attribute>) -> Vec<syn::Attribute> {
    let (specs, rest) = std::mem::take(attrs).into_iter().partition(is_spec_attr);
    *attrs = rest;
    specs
}

fn is_spec_attr(attr: &syn::Attribute) -> bool {
    let segments = &attr.path().segments;
    let mut idents = segments.iter().rev().map(|segment| &segment.ident);
    let Some(name) = idents.next() else {
        return false;
    };
    matches!(
        name.to_string().as_str(),
        "requires" | "ensures" | "_requires_ensures"
    ) && idents
        .next()
        .is_some_and(|module| module == "thrust_macros")
}

/// Rewrites the `Self::Assoc` projections a trait impl declares into their definitions,
/// so a signature copied out of the impl still means the same in an inherent impl.
struct SelfAssocResolver<'a> {
    assoc_types: &'a [(syn::Ident, syn::Type)],
}

impl VisitMut for SelfAssocResolver<'_> {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        syn::visit_mut::visit_type_mut(self, ty);

        let syn::Type::Path(type_path) = &*ty else {
            return;
        };
        if type_path.qself.is_some() || type_path.path.segments.len() != 2 {
            return;
        }
        let mut segments = type_path.path.segments.iter();
        if segments
            .next()
            .is_none_or(|segment| segment.ident != "Self")
        {
            return;
        }
        let projected = &segments.next().expect("two segments").ident;
        if let Some((_, definition)) = self.assoc_types.iter().find(|(name, _)| name == projected) {
            *ty = definition.clone();
        }
    }
}

/// Rewrites each spec macro in the body into its context-carrying counterpart and extends
/// the where clause with the `Model` predicates those calls need. A body naming no spec
/// macro — or a trait method that has no body at all — is left as it is.
fn expand_fn(mut func: FnItemWithSignature) -> TokenStream {
    let outer = match crate::extract_outer_context(func.attrs()) {
        Ok(outer) => outer,
        Err(e) => return e.to_compile_error().into(),
    };

    let host_sig = func.sig().clone();
    let mut injector = ContextInjector {
        sig: &host_sig,
        outer: outer.as_ref(),
        injected: false,
        self_used: false,
    };
    if let Some(body) = func.block_mut() {
        injector.visit_block_mut(body);
    }
    if !injector.injected {
        return func.into_token_stream().into();
    }

    let type_lowering = match &outer {
        Some(outer) => crate::FormulaFnTypeLowering::with_outer_context(&host_sig, outer),
        None => crate::FormulaFnTypeLowering::new(&host_sig),
    };
    let mut predicates = type_lowering.model_where_predicates();
    if injector.self_used {
        predicates.extend(type_lowering.model_where_predicates_for(&quote::format_ident!("Self")));
    }
    if !predicates.is_empty() {
        func.sig_mut()
            .generics
            .make_where_clause()
            .predicates
            .extend(predicates);
    }

    func.into_token_stream().into()
}

struct ContextInjector<'a> {
    sig: &'a Signature,
    outer: Option<&'a FnOuterItem>,
    injected: bool,
    self_used: bool,
}

impl ContextInjector<'_> {
    fn inject_context(&self, closure: &TokenStream2) -> TokenStream2 {
        let sig = self.sig;
        let outer_attr = self
            .outer
            .map(|outer| quote!(#[thrust::_outer_context(#outer)]));

        quote! {
            #outer_attr
            #sig;
            #closure
        }
    }
}

impl VisitMut for ContextInjector<'_> {
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        let Some(with_context) = context_carrying_form(&mac.path) else {
            return;
        };
        self.injected = true;
        if crate::tokens_contain_ident(&mac.tokens, "Self") {
            self.self_used = true;
        }
        mac.tokens = self.inject_context(&mac.tokens);
        mac.path = with_context;
    }
}

/// The context-carrying counterpart of a spec macro that takes a formula over live
/// variables, or `None` for any other macro.
fn context_carrying_form(path: &syn::Path) -> Option<syn::Path> {
    // TODO: identify the macro precisely
    match path.segments.last()?.ident.to_string().as_str() {
        "invariant" => Some(syn::parse_quote!(::thrust_macros::_invariant_with_context)),
        "ghost" => Some(syn::parse_quote!(::thrust_macros::_ghost_with_context)),
        _ => None,
    }
}
