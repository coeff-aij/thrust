//! Rewriting of a `for` loop whose body starts with an `invariant!` naming the iterator and its
//! history.
//!
//! The loop is desugared as Creusot does (`creusot-std-proc/src/creusot/invariant.rs`,
//! `desugar_for`): the iterator is a variable `iter`, `iter_old` a ghost copy of it before the
//! loop, and `produced` the ghost sequence of the items `next` has returned so far. The loop
//! invariant is the written one conjoined with the structural `inv(iter)` and
//! `produces(iter_old, produced, iter)` of `IteratorSpec`, and the written one may name `iter`, `iter_old` and `produced`. Those names
//! shadow variables of the same names in the loop body.

/// The desugaring of `for_loop`, or `None` when its body does not start with an `invariant!`
/// that has a parameter `iter`, whose type is the iterator's, and one named `iter_old` or
/// `produced`. An invariant naming `iter` alone needs no rewriting: rustc's own desugaring names
/// the iterator `iter`.
pub fn desugar(for_loop: &syn::ExprForLoop) -> Option<syn::Expr> {
    let (invariant, rest) = for_loop.body.stmts.split_first()?;
    let iter_ty = iterator_type(invariant)?;

    let syn::ExprForLoop {
        label, pat, expr, ..
    } = for_loop;
    // A struct literal is parenthesized in a `for` head, but not in the argument it becomes.
    let expr = match &**expr {
        syn::Expr::Paren(paren) => &paren.expr,
        expr => expr,
    };
    let seq: syn::Type = syn::parse_quote!(
        crate::thrust_models::model::Seq<
            <<#iter_ty as ::core::iter::Iterator>::Item as crate::thrust_models::Model>::Ty
        >
    );
    Some(syn::parse_quote!({
        let mut iter = ::core::iter::IntoIterator::into_iter(#expr);
        let iter_old = thrust_macros::ghost!(|iter: #iter_ty| -> #iter_ty { iter });
        let mut produced = thrust_macros::ghost!(|| -> #seq { crate::thrust_models::model::Seq::empty() });
        #label loop {
            #invariant
            thrust_macros::invariant!(
                |iter: #iter_ty,
                 iter_old: crate::thrust_models::Ghost<#iter_ty>,
                 produced: crate::thrust_models::Ghost<#seq>|
                <#iter_ty as crate::IteratorSpec>::inv(iter)
                    && <#iter_ty as crate::IteratorSpec>::produces(iter_old, produced, iter)
            );
            match ::core::iter::Iterator::next(&mut iter) {
                ::core::option::Option::Some(__thrust_item) => {
                    let __thrust_produced = thrust_macros::ghost!(
                        |produced: crate::thrust_models::Ghost<#seq>,
                         __thrust_item: <#iter_ty as ::core::iter::Iterator>::Item|
                        -> #seq { produced.push(__thrust_item) }
                    );
                    let _live = &produced;
                    produced = __thrust_produced;
                    let #pat = __thrust_item;
                    #(#rest)*
                }
                // The ghosts are named only by formulas, so a use keeps them live at the loop head.
                ::core::option::Option::None => {
                    let _live = (&iter_old, &produced);
                    break;
                }
            }
        }
    }))
}

/// The type of the parameter `iter` of `stmt`, an `invariant!(|..| ..)` that also names
/// `iter_old` or `produced`.
fn iterator_type(stmt: &syn::Stmt) -> Option<syn::Type> {
    let mac = match stmt {
        syn::Stmt::Macro(stmt) => &stmt.mac,
        syn::Stmt::Expr(syn::Expr::Macro(expr), _) => &expr.mac,
        _ => return None,
    };
    if mac.path.segments.last()?.ident != "invariant" {
        return None;
    }
    let closure: syn::ExprClosure =
        syn::parse2(crate::formula::wrap_closure_body(mac.tokens.clone())).ok()?;
    let params: Vec<(&syn::Ident, &syn::Type)> = closure
        .inputs
        .iter()
        .filter_map(|input| {
            let syn::Pat::Type(pat_type) = input else {
                return None;
            };
            let syn::Pat::Ident(pat_ident) = &*pat_type.pat else {
                return None;
            };
            Some((&pat_ident.ident, &*pat_type.ty))
        })
        .collect();
    if !params
        .iter()
        .any(|(name, _)| *name == "iter_old" || *name == "produced")
    {
        return None;
    }
    params
        .iter()
        .find(|(name, _)| *name == "iter")
        .map(|(_, ty)| (*ty).clone())
}
