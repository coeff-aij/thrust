//! Expansion of `thrust_macros::invariant!`, its partial counterpart
//! `thrust_macros::partial_invariant!`, the statement forms `thrust_macros::proof_assert!` and
//! `thrust_macros::assume!`, and their context-carrying siblings
//! (`thrust_macros::_invariant_with_context!` and so on).
//!
//! The forms differ only in the marker they call: an `invariant!` is the loop head's whole
//! invariant, a `partial_invariant!` is conjoined with the inferred one, a `proof_assert!` is
//! checked where it is written and assumed after it, an `assume!` is assumed there unchecked, and
//! a `block_requires!` and the `block_ensures!` after it are the contract of the code between
//! them.
//!
//! All expand a predicate closure with explicit parameter types into a
//! `#[thrust::formula_fn]` over `Model::Ty` parameters plus a marker call
//! referencing it; they share [`expand_invariant`] and differ only in input:
//!
//! - `invariant!(|x: i64| x >= 1)` takes a bare predicate closure and only sees
//!   concrete types.
//! - `_invariant_with_context!(..)` additionally carries the enclosing generic
//!   context (see [`mod@crate::formula_fn_lifting`]). It is never written by hand:
//!   `#[thrust_macros::context]` rewrites each `invariant!` it finds into this form,
//!   pasting the host function's signature (and, in methods, a
//!   `#[thrust::_outer_context(..)]` attribute carrying the enclosing `impl`/`trait`
//!   header) ahead of the closure:
//!
//!   ```ignore
//!   _invariant_with_context!(
//!       #[thrust::_outer_context(impl<T> Foo<T> where ..)]  // methods only
//!       fn f<U>(..) -> .. where ..;                         // host signature, as-is
//!       |x: T, v: T| x == v
//!   )
//!   ```

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, ToTokens};
use syn::FnArg;

use crate::formula_fn_lifting::{self, ClosureWithLocalTypes, EnclosingContext, LiftedFormulaFn};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// The marker function a form calls.
#[derive(Clone, Copy)]
pub enum Marker {
    Full,
    Partial,
    Assert,
    Assume,
    BlockRequires,
    BlockEnsures,
}

impl Marker {
    /// The invariant form a macro named `name` is, or `None` for any other macro.
    pub fn of_macro(name: &str) -> Option<Self> {
        match name {
            "invariant" => Some(Marker::Full),
            "partial_invariant" => Some(Marker::Partial),
            _ => None,
        }
    }

    /// The statement form a macro named `name` is, or `None` for any other macro.
    pub fn statement_of_macro(name: &str) -> Option<Self> {
        match name {
            "proof_assert" => Some(Marker::Assert),
            "assume" => Some(Marker::Assume),
            "block_requires" => Some(Marker::BlockRequires),
            "block_ensures" => Some(Marker::BlockEnsures),
            _ => None,
        }
    }

    /// Whether the form is a statement (`proof_assert!`, `assume!`, `block_requires!`,
    /// `block_ensures!`), whose closure may leave a closure local's type to the local (`|f: _|`,
    /// `<P: Fn(i64) -> i64> |w: Wrap<P>|`).
    fn is_statement(self) -> bool {
        match self {
            Marker::Assert | Marker::Assume | Marker::BlockRequires | Marker::BlockEnsures => true,
            Marker::Full | Marker::Partial => false,
        }
    }

    /// The context-carrying counterpart `#[thrust_macros::context]` rewrites the form into.
    pub fn with_context_path(self) -> syn::Path {
        match self {
            Marker::Full => syn::parse_quote!(::thrust_macros::_invariant_with_context),
            Marker::Partial => {
                syn::parse_quote!(::thrust_macros::_partial_invariant_with_context)
            }
            Marker::Assert => syn::parse_quote!(::thrust_macros::_proof_assert_with_context),
            Marker::Assume => syn::parse_quote!(::thrust_macros::_assume_with_context),
            Marker::BlockRequires => {
                syn::parse_quote!(::thrust_macros::_block_requires_with_context)
            }
            Marker::BlockEnsures => syn::parse_quote!(::thrust_macros::_block_ensures_with_context),
        }
    }

    fn ident(self) -> syn::Ident {
        match self {
            Marker::Full => format_ident!("__invariant_marker"),
            Marker::Partial => format_ident!("__partial_invariant_marker"),
            Marker::Assert => format_ident!("__assert_marker"),
            Marker::Assume => format_ident!("__assume_marker"),
            Marker::BlockRequires => format_ident!("__block_requires_marker"),
            Marker::BlockEnsures => format_ident!("__block_ensures_marker"),
        }
    }

    /// The prefix of the name of the formula function the form expands into.
    fn item_prefix(self) -> &'static str {
        match self {
            Marker::Full | Marker::Partial => "_thrust_invariant",
            Marker::Assert => "_thrust_assert",
            Marker::Assume => "_thrust_assume",
            Marker::BlockRequires => "_thrust_block_requires",
            Marker::BlockEnsures => "_thrust_block_ensures",
        }
    }
}

/// Expands `invariant!(CLOSURE)` (or another form): a bare predicate closure with no threaded
/// context.
pub fn expand(input: TokenStream, marker: Marker) -> TokenStream {
    if let Some(e) = crate::loop_label::outside_context_error(&input.clone().into()) {
        return e.to_compile_error().into();
    }
    let input = match rename_entry_values(input.into(), marker) {
        Ok(input) => input,
        Err(e) => return e.to_compile_error().into(),
    };
    let input = crate::formula::wrap_closure_body(input);
    let ClosureWithLocalTypes {
        local_types,
        closure,
    } = match syn::parse2::<ClosureWithLocalTypes>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_invariant(&closure, &local_types, None, marker) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Expands `_invariant_with_context!(#outer_attr #sig; CLOSURE)`, the form
/// `#[thrust_macros::context]` rewrites each `invariant!` into.
pub fn expand_with_context(input: TokenStream, marker: Marker) -> TokenStream {
    let input = match rename_entry_values(input.into(), marker) {
        Ok(input) => input,
        Err(e) => return e.to_compile_error().into(),
    };
    let input = crate::formula::wrap_closure_body(input);
    let parser = |input: syn::parse::ParseStream| {
        let context: EnclosingContext = input.parse()?;
        let closure: ClosureWithLocalTypes = input.parse()?;
        Ok((context, closure))
    };
    let (
        context,
        ClosureWithLocalTypes {
            local_types,
            closure,
        },
    ) = match syn::parse::Parser::parse2(parser, input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_invariant(&closure, &local_types, Some(&context), marker) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// `input` with the `old!(x)` of a loop invariant or a `proof_assert!` renamed
/// ([`mod@crate::entry_value`]); the other statement forms take no `old!`.
fn rename_entry_values(
    input: proc_macro2::TokenStream,
    marker: Marker,
) -> syn::Result<proc_macro2::TokenStream> {
    match marker {
        Marker::Full | Marker::Partial | Marker::Assert => {
            crate::entry_value::rename_in_invariant(input)
        }
        Marker::Assume | Marker::BlockRequires | Marker::BlockEnsures => {
            crate::entry_value::reject(&input)?;
            Ok(input)
        }
    }
}

/// Expands a predicate closure into a `#[thrust::formula_fn]` plus a marker call.
fn expand_invariant(
    closure: &syn::ExprClosure,
    local_types: &syn::Generics,
    context: Option<&EnclosingContext>,
    marker: Marker,
) -> syn::Result<syn::Expr> {
    if !marker.is_statement() && !local_types.params.is_empty() {
        return Err(syn::Error::new_spanned(
            local_types,
            "a loop invariant cannot leave a type to a local; only `proof_assert!`, `assume!`, \
             `block_requires!` and `block_ensures!` can",
        ));
    }
    let mut params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "closure parameters must have explicit types, e.g. `|x: i64| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        params.push(syn::parse_quote!(#pat: #ty));
    }

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("{}_{}", marker.item_prefix(), id);
    let lifted = if marker.is_statement() {
        formula_fn_lifting::lift_statement(&name, &params, &closure.body, context, local_types)
    } else {
        formula_fn_lifting::lift(&name, &params, &closure.body, context)
    };
    let LiftedFormulaFn { item, reference } = lifted?;
    let marker = marker.ident();

    Ok(syn::parse_quote!({
        #item

        crate::thrust_models::#marker(#reference)
    }))
}
