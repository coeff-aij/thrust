//! Expansion of `thrust_macros::invariant!`, its partial counterpart
//! `thrust_macros::invariant_hint!`, and their context-carrying siblings
//! `thrust_macros::_invariant_with_context!` and `_invariant_hint_with_context!`.
//!
//! The two forms differ only in the marker they call: an `invariant!` is the loop
//! head's whole invariant, an `invariant_hint!` is conjoined with the inferred one.
//!
//! Both expand a predicate closure with explicit parameter types into a
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

use crate::formula_fn_lifting::{self, ClosureWithContext, EnclosingContext, LiftedFormulaFn};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// The marker function an invariant form calls.
#[derive(Clone, Copy)]
pub enum Marker {
    Full,
    Partial,
}

impl Marker {
    fn ident(self) -> syn::Ident {
        match self {
            Marker::Full => format_ident!("__invariant_marker"),
            Marker::Partial => format_ident!("__invariant_hint_marker"),
        }
    }
}

/// Expands `invariant!(CLOSURE)`: a bare predicate closure with no threaded
/// context.
pub fn expand(input: TokenStream, marker: Marker) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let closure = match syn::parse2::<syn::ExprClosure>(input) {
        Ok(closure) => closure,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_invariant(&closure, None, marker) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Expands `_invariant_with_context!(#outer_attr #sig; CLOSURE)`, the form
/// `#[thrust_macros::context]` rewrites each `invariant!` into.
pub fn expand_with_context(input: TokenStream, marker: Marker) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let ClosureWithContext { closure, context } = match syn::parse2::<ClosureWithContext>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_invariant(&closure, Some(&context), marker) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Expands a predicate closure into a `#[thrust::formula_fn]` plus a marker call.
fn expand_invariant(
    closure: &syn::ExprClosure,
    context: Option<&EnclosingContext>,
    marker: Marker,
) -> syn::Result<syn::Expr> {
    let mut params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "invariant closure parameters must have explicit types, e.g. `|x: i64| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        params.push(syn::parse_quote!(#pat: #ty));
    }

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("_thrust_invariant_{}", id);
    let LiftedFormulaFn { item, reference } =
        formula_fn_lifting::lift(&name, &params, &closure.body, context)?;
    let marker = marker.ident();

    Ok(syn::parse_quote!({
        #item

        crate::thrust_models::#marker(#reference)
    }))
}
