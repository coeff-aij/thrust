//! Rewriting of a `for` loop whose body starts with `invariant!` or `partial_invariant!` calls
//! naming the iterator.
//!
//! The loop is desugared as Creusot does (`creusot-std-proc/src/creusot/invariant.rs`,
//! `desugar_for`): the iterator is a variable, stepped by `Iterator::next` at the loop head, where
//! the invariant is, and the invariant names it `iter`. When the invariant also names `iter_old`
//! or `produced`, those are ghosts too: `iter_old` a copy of the iterator before the loop, and
//! `produced` the sequence of the items `next` has returned so far, and the invariant is conjoined
//! with the structural `inv(iter)` and `produces(iter_old, produced, iter)` of `IteratorSpec`.
//!
//! The variables get names of their own for each loop, and the invariant's `iter`, `iter_old` and
//! `produced` are renamed to them, so the loop body sees its own variables of those names, and an
//! annotated loop nested in another `for` finds its own iterator.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro2::{Ident, TokenStream, TokenTree};
use quote::format_ident;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// The desugaring of `for_loop`, or `None` when its body does not start with `invariant!` or
/// `partial_invariant!` calls one of which has a parameter `iter`, whose type is the iterator's.
/// Every invariant of that leading run names the loop's ghosts.
pub fn desugar(for_loop: &syn::ExprForLoop) -> Option<syn::Expr> {
    let stmts = &for_loop.body.stmts;
    let leading: Vec<_> = stmts.iter().map_while(invariant_params).collect();
    let (invariants, rest) = stmts.split_at(leading.len());
    let params: Vec<_> = leading.into_iter().flatten().collect();
    let iter_ty = params
        .iter()
        .find(|(name, _)| name == "iter")
        .map(|(_, ty)| ty.clone())?;
    let names_history = params
        .iter()
        .any(|(name, _)| name == "iter_old" || name == "produced");

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
        .map(|invariant| rename_in_stmt(invariant, &renames))
        .collect();

    let syn::ExprForLoop {
        label, pat, expr, ..
    } = for_loop;
    // A struct literal is parenthesized in a `for` head, but not in the argument it becomes.
    let expr = match &**expr {
        syn::Expr::Paren(paren) => &paren.expr,
        expr => expr,
    };
    // As in rustc's lowering, the iterator is bound by a `match`, so that the temporaries of the
    // `for` head live as long as the loop. The type the invariant gives `iter` is checked by rustc
    // against the iterator's.
    if !names_history {
        return Some(syn::parse_quote!(
            match ::core::iter::IntoIterator::into_iter(#expr) {
                mut #iter => #label loop {
                    let _: &#iter_ty = &#iter;
                    #(#invariants)*
                    match ::core::iter::Iterator::next(&mut #iter) {
                        ::core::option::Option::Some(#item) => {
                            let #pat = #item;
                            #(#rest)*
                        }
                        ::core::option::Option::None => break,
                    }
                }
            }
        ));
    }

    let seq: syn::Type = syn::parse_quote!(
        crate::thrust_models::model::Seq<
            <<#iter_ty as ::core::iter::Iterator>::Item as crate::thrust_models::Model>::Ty
        >
    );
    let next_produced = format_ident!("__thrust_for_next_produced_{}", n);
    let live = format_ident!("__thrust_for_live_{}", n);
    Some(syn::parse_quote!(
        match ::core::iter::IntoIterator::into_iter(#expr) {
            mut #iter => {
                let _: &#iter_ty = &#iter;
                let #iter_old = thrust_macros::ghost!(|#iter: #iter_ty| -> #iter_ty { #iter });
                let mut #produced = thrust_macros::ghost!(|| -> #seq { crate::thrust_models::model::Seq::empty() });
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
                            break;
                        }
                    }
                }
            }
        }
    ))
}

/// `stmt`, an invariant macro, with each identifier `from` that is not a field, method or path
/// segment replaced by `to`.
fn rename_in_stmt(stmt: &syn::Stmt, renames: &[(&str, &Ident)]) -> syn::Stmt {
    let mut stmt = stmt.clone();
    let mac = match &mut stmt {
        syn::Stmt::Macro(stmt) => &mut stmt.mac,
        syn::Stmt::Expr(syn::Expr::Macro(expr), _) => &mut expr.mac,
        _ => return stmt,
    };
    mac.tokens = rename_tokens(mac.tokens.clone(), renames);
    stmt
}

fn rename_tokens(tokens: TokenStream, renames: &[(&str, &Ident)]) -> TokenStream {
    let mut after_access = false;
    tokens
        .into_iter()
        .map(|token| {
            let renamed = match token {
                TokenTree::Group(group) => {
                    let mut renamed = proc_macro2::Group::new(
                        group.delimiter(),
                        rename_tokens(group.stream(), renames),
                    );
                    renamed.set_span(group.span());
                    TokenTree::Group(renamed)
                }
                TokenTree::Ident(ident) if !after_access => renames
                    .iter()
                    .find(|(from, _)| ident == from)
                    .map(|(_, to)| TokenTree::Ident(Ident::new(&to.to_string(), ident.span())))
                    .unwrap_or(TokenTree::Ident(ident)),
                token => token,
            };
            after_access =
                matches!(&renamed, TokenTree::Punct(p) if p.as_char() == '.' || p.as_char() == ':');
            renamed
        })
        .collect()
}

/// The typed parameters of `stmt` when it is an `invariant!(|..| ..)` or a `partial_invariant!`.
fn invariant_params(stmt: &syn::Stmt) -> Option<Vec<(syn::Ident, syn::Type)>> {
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
                let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                    return None;
                };
                Some((pat_ident.ident.clone(), (*pat_type.ty).clone()))
            })
            .collect(),
    )
}
