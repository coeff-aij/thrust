//! Expansion of `thrust_macros::ghost!`, `thrust_macros::choose!` and their context-carrying
//! siblings `thrust_macros::_ghost_with_context!` and `thrust_macros::_choose_with_context!` into
//! a `#[thrust::formula_fn]` relating the introduced value to the ghost term, plus a marker call
//! the analyzer intercepts. A `choose!` takes a formula in place of the term, and relates the
//! value to it as `thrust_models::witness(formula, value)`: the value is a witness of it.
//!
//! The value is parameter `0`, as in an `ensures` formula function: that is the layout
//! the analyzer reads the term back with. Unlike `ensures`, it is bound to a synthetic
//! name, leaving `result` free for a term to name a live variable with.
//!
//! `ghost!(|x: i64| -> Seq<Int> { .. })` only sees concrete types.
//! `_ghost_with_context!(..)` additionally carries the enclosing generic context (see
//! [`mod@crate::formula_fn_lifting`]), so a term may name generic- and `Self`-typed
//! variables; `#[thrust_macros::context]` rewrites each `ghost!` it finds into
//! that form.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, ToTokens};
use syn::FnArg;

use crate::formula_fn_lifting::{self, ClosureWithContext, EnclosingContext, LiftedFormulaFn};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// What the closure's body gives the value.
#[derive(Clone, Copy)]
pub enum Form {
    /// `ghost!`: the value is the term.
    Term,
    /// `choose!`: the value is a witness of the formula.
    Witness,
}

impl Form {
    fn marker(self) -> syn::Ident {
        match self {
            Form::Term => format_ident!("__ghost_marker"),
            Form::Witness => format_ident!("__choose_marker"),
        }
    }

    fn item_prefix(self) -> &'static str {
        match self {
            Form::Term => "_thrust_ghost",
            Form::Witness => "_thrust_choose",
        }
    }

    /// The body of the formula function relating `value` to the closure's `body`.
    fn relation(self, value: &syn::Ident, body: &syn::Expr) -> syn::Expr {
        match self {
            Form::Term => {
                syn::parse_quote!(crate::thrust_models::log_eq_args(&#value, &(#body)).log_eq())
            }
            Form::Witness => syn::parse_quote!(crate::thrust_models::witness(#body, #value)),
        }
    }
}

/// Expands `ghost!(CLOSURE)` or `choose!(CLOSURE)`: a bare ghost term with no threaded context.
pub fn expand(input: TokenStream, form: Form) -> TokenStream {
    if let Some(e) = crate::loop_label::outside_context_error(&input.clone().into()) {
        return e.to_compile_error().into();
    }
    let input = crate::formula::wrap_closure_body(input.into());
    let closure = match syn::parse2::<syn::ExprClosure>(input) {
        Ok(closure) => closure,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_ghost(&closure, None, form) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Expands `_ghost_with_context!(#outer_attr #sig; CLOSURE)`, the form
/// `#[thrust_macros::context]` rewrites each `ghost!` into, or `_choose_with_context!`.
pub fn expand_with_context(input: TokenStream, form: Form) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let ClosureWithContext { closure, context } = match syn::parse2::<ClosureWithContext>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_ghost(&closure, Some(&context), form) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn expand_ghost(
    closure: &syn::ExprClosure,
    context: Option<&EnclosingContext>,
    form: Form,
) -> syn::Result<syn::Expr> {
    let syn::ReturnType::Type(_, value_ty) = &closure.output else {
        return Err(syn::Error::new_spanned(
            closure,
            "ghost expression must have an explicit type, e.g. `|x: i64| -> Seq<Int> { .. }`",
        ));
    };

    // Synthetic, so that a term may name a live variable called `result`.
    let value = format_ident!("__thrust_ghost_value");
    let mut params: Vec<FnArg> = vec![syn::parse_quote!(#value: #value_ty)];
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "ghost expression parameters must have explicit types, e.g. `|x: i64| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        params.push(syn::parse_quote!(#pat: #ty));
    }

    let body = form.relation(&value, &closure.body);

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("{}_{}", form.item_prefix(), id);
    let LiftedFormulaFn { item, reference } =
        formula_fn_lifting::lift(&name, &params, &body, context)?;
    let marker = form.marker();

    Ok(syn::parse_quote!({
        #item

        crate::thrust_models::#marker::<_, #value_ty>(#reference)
    }))
}
