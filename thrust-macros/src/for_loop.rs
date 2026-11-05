//! Rewriting of a `for` loop whose body starts with `invariant!` or `partial_invariant!` calls
//! naming the iterator, or with no invariant.
//!
//! The loop is desugared as Creusot does (`creusot-std-proc/src/creusot/invariant.rs`,
//! `desugar_for`): the iterator is a variable, stepped by `Iterator::next` at the loop head, where
//! the invariant is, and the invariant names it `iter`. When the invariant also names `iter_old`
//! or `produced`, those are ghosts too: `iter_old` a copy of the iterator before the loop, and
//! `produced` the sequence of the items `next` has returned so far, and the invariant is conjoined
//! with the structural `inv(iter)` and `produces(iter_old, produced, iter)` of `IteratorSpec`.
//!
//! With `THRUST_FOR_LOOP_HISTORY=1`, a loop with no invariant gets the same ghosts, and
//! `inv(iter)` and `produces(iter_old, produced, iter)` are conjoined to the invariant Thrust
//! infers, so that the inferred part can relate the loop's state to `produced`, as Creusot does
//! for every loop.
//!
//! The variables of an annotated loop get names of their own for each loop, and the invariant's
//! `iter`, `iter_old` and `produced` are renamed to them, so the loop body sees its own variables
//! of those names, and an annotated loop nested in another `for` finds its own iterator. A
//! labelled loop also renames the references `iter!('l)`, `iter_old!('l)` and `produced!('l)` to
//! its label in the specifications of its body (see [`mod@crate::loop_label`]). A labelled loop
//! with no invariant whose label a specification of its body references is desugared as an
//! annotated one with no written invariant, so that `iter!('l)` names its iterator while Thrust
//! infers its invariant; it has no `iter_old` or `produced` to name, and
//! `THRUST_FOR_LOOP_HISTORY` gives it none.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::format_ident;
use syn::spanned::Spanned as _;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// The desugaring of `for_loop`, or `None` when its body starts with `invariant!` or
/// `partial_invariant!` calls none of which has a parameter `iter`, whose type is the iterator's,
/// or with no invariant, no reference to the loop's label in the specifications of its body and
/// `THRUST_FOR_LOOP_HISTORY` not `1`. Every invariant of that leading run names the loop's ghosts.
pub fn desugar(for_loop: &syn::ExprForLoop) -> Option<syn::Expr> {
    let label_name = for_loop.label.as_ref().map(|label| label.name.to_string());
    let label_name = label_name.as_deref();
    let stmts = &for_loop.body.stmts;
    let leading: Vec<_> = stmts
        .iter()
        .map_while(|stmt| invariant_params(stmt, label_name))
        .collect();
    let named_by_label =
        label_name.is_some_and(|label| crate::loop_label::is_referenced_in_body(stmts, label));
    if leading.is_empty() && !named_by_label {
        return history_requested().then(|| desugar_with_inferred_invariant(for_loop));
    }
    let (invariants, rest) = stmts.split_at(leading.len());
    let mut params: Vec<_> = leading.into_iter().flatten().collect();
    if !invariants.is_empty() && !params.iter().any(|(name, _)| name == "iter") {
        return None;
    }

    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    let iter = format_ident!("__thrust_for_iter_{}", n);
    let iter_old = format_ident!("__thrust_for_iter_old_{}", n);
    let produced = format_ident!("__thrust_for_produced_{}", n);
    let item = format_ident!("__thrust_for_item_{}", n);
    let renames = [
        ("iter", &iter),
        ("iter_old", &iter_old),
        ("produced", &produced),
    ];
    let invariants: Vec<_> = invariants
        .iter()
        .map(|invariant| rename_in_stmt(invariant, label_name, &renames))
        .collect();
    let mut rest = rest.to_vec();
    if let Some(label_name) = label_name {
        params.extend(crate::loop_label::rename_in_body(
            &mut rest, label_name, &renames,
        ));
    }
    let names_history = params
        .iter()
        .any(|(name, _)| name == "iter_old" || name == "produced");
    let iter_checks = type_checks(&params, "iter", &iter);

    let syn::ExprForLoop {
        label, pat, expr, ..
    } = for_loop;
    let break_label = label.as_ref().map(|label| &label.name);
    let expr = head_expr(expr);
    // As in rustc's lowering, the iterator is bound by a `match`, so that the temporaries of the
    // `for` head live as long as the loop.
    if !names_history {
        return Some(syn::parse_quote!(
            match ::core::iter::IntoIterator::into_iter(#expr) {
                mut #iter => #label loop {
                    #iter_checks
                    #(#invariants)*
                    match ::core::iter::Iterator::next(&mut #iter) {
                        ::core::option::Option::Some(#item) => {
                            let #pat = #item;
                            #(#rest)*
                        }
                        ::core::option::Option::None => break #break_label,
                    }
                }
            }
        ));
    }

    let iter_ty = params
        .iter()
        .find(|(name, _)| name == "iter")
        .map(|(_, ty)| ty.clone())?;
    let seq: syn::Type = syn::parse_quote!(
        crate::thrust_models::model::Seq<
            <<#iter_ty as ::core::iter::Iterator>::Item as crate::thrust_models::Model>::Ty
        >
    );
    let iter_old_checks = type_checks(&params, "iter_old", &iter_old);
    let produced_checks = type_checks(&params, "produced", &produced);
    let next_produced = format_ident!("__thrust_for_next_produced_{}", n);
    let live = format_ident!("__thrust_for_live_{}", n);
    Some(syn::parse_quote!(
        match ::core::iter::IntoIterator::into_iter(#expr) {
            mut #iter => {
                #iter_checks
                let #iter_old = thrust_macros::ghost!(|#iter: #iter_ty| -> #iter_ty { #iter });
                #iter_old_checks
                let mut #produced = thrust_macros::ghost!(|| -> #seq { crate::thrust_models::model::Seq::empty() });
                #produced_checks
                #label loop {
                    #(#invariants)*
                    thrust_macros::invariant!(
                        |#iter: #iter_ty,
                         #iter_old: crate::thrust_models::Ghost<#iter_ty>,
                         #produced: crate::thrust_models::Ghost<#seq>|
                        <#iter_ty as crate::IteratorSpec>::inv(#iter)
                            && <#iter_ty as crate::IteratorSpec>::produces(#iter_old, #produced, #iter)
                    );
                    match ::core::iter::Iterator::next(&mut #iter) {
                        ::core::option::Option::Some(#item) => {
                            let #next_produced = thrust_macros::ghost!(
                                |#produced: crate::thrust_models::Ghost<#seq>,
                                 #item: <#iter_ty as ::core::iter::Iterator>::Item|
                                -> #seq { #produced.push(#item) }
                            );
                            let #live = &#produced;
                            #produced = #next_produced;
                            let #pat = #item;
                            #(#rest)*
                        }
                        // The ghosts are named only by formulas, so a use keeps them live at the loop head.
                        ::core::option::Option::None => {
                            let #live = (&#iter_old, &#produced);
                            break #break_label;
                        }
                    }
                }
            }
        }
    ))
}

/// The desugaring of `for_loop`, whose body starts with no invariant, for Thrust to infer its
/// invariant: as with a written one, except that the iterator's type cannot be written, so the
/// ghosts are made by functions generic in it, and `inv(iter)` and
/// `produces(iter_old, produced, iter)` are conjoined to the inferred invariant by a marker call
/// that names them in its scope (`thrust_models::__for_loop_history_marker`). The names are the
/// same for each loop: the innermost loop's shadow those of the loops around it.
fn desugar_with_inferred_invariant(for_loop: &syn::ExprForLoop) -> syn::Expr {
    let syn::ExprForLoop {
        label,
        pat,
        expr,
        body,
        ..
    } = for_loop;
    let expr = head_expr(expr);
    let stmts = &body.stmts;
    let iter = format_ident!("__thrust_for_iter");
    let iter_old = format_ident!("__thrust_for_iter_old");
    let produced = format_ident!("__thrust_for_produced");
    let item = format_ident!("__thrust_for_item");
    syn::parse_quote!(
        match ::core::iter::IntoIterator::into_iter(#expr) {
            mut #iter => {
                let #iter_old = crate::thrust_models::__for_loop_iter_old(&#iter);
                let mut #produced = crate::thrust_models::__for_loop_produced(&#iter);
                #label loop {
                    crate::thrust_models::__for_loop_history_marker(#iter_old, #produced);
                    match ::core::iter::Iterator::next(&mut #iter) {
                        ::core::option::Option::Some(#item) => {
                            #produced = crate::thrust_models::__for_loop_produced_push(#produced, &#item);
                            let #pat = #item;
                            #(#stmts)*
                        }
                        ::core::option::Option::None => break,
                    }
                }
            }
        }
    )
}

/// The ghosts of a `for` loop that a reference to its label can name.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LabelledGhosts {
    /// `iter`, `iter_old` and `produced`: the body starts with an `invariant!` or
    /// `partial_invariant!` naming `iter`.
    All,
    /// `iter` only: the body starts with no invariant, so Thrust infers it, and the loop keeps no
    /// history for a reference to name.
    Iter,
    /// None: the body starts with invariants none of which names `iter`.
    None,
}

/// The ghosts of `for_loop` that a reference to its label can name.
pub fn labelled_ghosts(for_loop: &syn::ExprForLoop) -> LabelledGhosts {
    let label = for_loop.label.as_ref().map(|label| label.name.to_string());
    let leading: Vec<_> = for_loop
        .body
        .stmts
        .iter()
        .map_while(|stmt| invariant_params(stmt, label.as_deref()))
        .collect();
    if leading.is_empty() {
        return LabelledGhosts::Iter;
    }
    if leading
        .into_iter()
        .flatten()
        .any(|(name, _)| name == "iter")
    {
        LabelledGhosts::All
    } else {
        LabelledGhosts::None
    }
}

/// Whether a loop with no invariant is to get the ghost history (`THRUST_FOR_LOOP_HISTORY=1`).
fn history_requested() -> bool {
    std::env::var("THRUST_FOR_LOOP_HISTORY").is_ok_and(|v| v == "1")
}

/// The iterator expression of a `for` head. A struct literal is parenthesized there, but not in
/// the argument it becomes.
fn head_expr(expr: &syn::Expr) -> &syn::Expr {
    match expr {
        syn::Expr::Paren(paren) => &paren.expr,
        expr => expr,
    }
}

/// Statements checking that each type the invariants give the parameter `name` is the type of
/// `var`. `(&var,)` is built inside another tuple and projected out, so that the annotation's
/// expected type does not reach it, and a tuple value is not coerced: rustc compares the types as
/// they are. A reference alone would be coerced, through `Deref` among others, and so would the
/// fields of a tuple expression checked against the annotation. Only temporaries are made, so
/// that nothing of the check is part of the loop's state.
fn type_checks(params: &[(Ident, syn::Type)], name: &str, var: &Ident) -> TokenStream {
    params
        .iter()
        .filter(|(param, _)| param == name)
        .map(|(_, ty)| {
            let var = Ident::new(&var.to_string(), ty.span());
            quote::quote_spanned!(ty.span()=> let _: (&#ty,) = ((&#var,),).0;)
        })
        .collect()
}

/// `stmt`, an invariant macro, with each identifier `from` that is not a field, method or path
/// segment, nor the name in a reference `from!('l)` to a loop label, replaced by `to`, and each
/// reference to the loop's label `label` replaced as `from` is.
fn rename_in_stmt(stmt: &syn::Stmt, label: Option<&str>, renames: &[(&str, &Ident)]) -> syn::Stmt {
    let mut stmt = stmt.clone();
    let mac = match &mut stmt {
        syn::Stmt::Macro(stmt) => &mut stmt.mac,
        syn::Stmt::Expr(syn::Expr::Macro(expr), _) => &mut expr.mac,
        _ => return stmt,
    };
    if let Some(label) = label {
        crate::loop_label::rename_macro(mac, label, renames);
    }
    mac.tokens = rename_tokens(mac.tokens.clone(), renames);
    stmt
}

fn rename_tokens(tokens: TokenStream, renames: &[(&str, &Ident)]) -> TokenStream {
    let tokens: Vec<TokenTree> = tokens.into_iter().collect();
    let mut after_access = false;
    let mut renamed = Vec::with_capacity(tokens.len());
    for (i, token) in tokens.iter().enumerate() {
        let in_reference = crate::loop_label::reference_at(&tokens[i..]).is_some();
        let token = match token {
            TokenTree::Group(group) => {
                let mut renamed = proc_macro2::Group::new(
                    group.delimiter(),
                    rename_tokens(group.stream(), renames),
                );
                renamed.set_span(group.span());
                TokenTree::Group(renamed)
            }
            TokenTree::Ident(ident) if !after_access && !in_reference => renames
                .iter()
                .find(|(from, _)| ident == from)
                .map(|(_, to)| TokenTree::Ident(Ident::new(&to.to_string(), ident.span())))
                .unwrap_or_else(|| token.clone()),
            token => token.clone(),
        };
        after_access =
            matches!(&token, TokenTree::Punct(p) if p.as_char() == '.' || p.as_char() == ':');
        renamed.push(token);
    }
    renamed.into_iter().collect()
}

/// The typed parameters of `stmt` when it is an `invariant!(|..| ..)` or a `partial_invariant!`.
/// A parameter that is a reference to `label`, the loop's own, counts as the ghost it names.
fn invariant_params(stmt: &syn::Stmt, label: Option<&str>) -> Option<Vec<(syn::Ident, syn::Type)>> {
    let mac = match stmt {
        syn::Stmt::Macro(stmt) => &stmt.mac,
        syn::Stmt::Expr(syn::Expr::Macro(expr), _) => &expr.mac,
        _ => return None,
    };
    crate::invariant::Marker::of_macro(&mac.path.segments.last()?.ident.to_string())?;
    let closure: syn::ExprClosure =
        syn::parse2(crate::formula::wrap_closure_body(mac.tokens.clone())).ok()?;
    Some(
        closure
            .inputs
            .iter()
            .filter_map(|input| {
                let syn::Pat::Type(pat_type) = input else {
                    return None;
                };
                match &*pat_type.pat {
                    syn::Pat::Ident(pat_ident) => {
                        Some((pat_ident.ident.clone(), (*pat_type.ty).clone()))
                    }
                    _ => crate::loop_label::typed_reference(pat_type, label?),
                }
            })
            .collect(),
    )
}
