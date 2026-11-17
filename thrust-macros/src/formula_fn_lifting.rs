//! Lifting a formula written inside a function body into a standalone
//! `#[thrust::formula_fn]` item that a marker call refers to.
//!
//! The item is a free function, so it inherits neither the enclosing function's generics
//! nor `Self`: a formula naming a generic- or `Self`-typed variable only type-checks once
//! those are re-declared on it and instantiated where it is referred to.
//! [`EnclosingContext`] carries what to re-declare, threaded in by
//! `#[thrust_macros::context]`; without it a formula only sees concrete types.

use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    visit_mut::VisitMut,
    FnArg, GenericParam, Signature, WherePredicate,
};

use crate::{fn_outer_item::FnOuterItem, FormulaFnTypeLowering};

/// The context a formula is written in: the host function's signature and, for a method,
/// its `impl`/`trait` header.
pub struct EnclosingContext {
    sig: Signature,
    outer: Option<FnOuterItem>,
}

impl Parse for EnclosingContext {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        let outer = crate::extract_outer_context(&attrs)?;
        let sig: Signature = input.parse()?;
        input.parse::<syn::Token![;]>()?;
        Ok(Self { sig, outer })
    }
}

impl EnclosingContext {
    /// Gives this context to the spec macros nested in `expr` (`context::inject_into_expr`).
    pub fn inject_into(&self, expr: &mut syn::Expr) {
        crate::context::inject_into_expr(&self.sig, self.outer.as_ref(), expr);
    }

    /// The generic params in scope: the host signature's own, plus the outer
    /// `impl`/`trait`'s for a method.
    fn generic_params(&self) -> impl Iterator<Item = &GenericParam> {
        self.sig
            .generics
            .params
            .iter()
            .chain(self.outer.iter().flat_map(|o| o.generics().params.iter()))
    }

    /// The where-predicates in scope, from the host signature and (for a method) the
    /// outer `impl`/`trait`.
    fn where_predicates(&self) -> impl Iterator<Item = &WherePredicate> {
        fn preds(g: &syn::Generics) -> impl Iterator<Item = &WherePredicate> {
            g.where_clause.iter().flat_map(|wc| wc.predicates.iter())
        }
        preds(&self.sig.generics).chain(self.outer.iter().flat_map(|o| preds(o.generics())))
    }

    fn type_lowering(&self) -> FormulaFnTypeLowering<'_> {
        match &self.outer {
            Some(outer) => FormulaFnTypeLowering::with_outer_context(&self.sig, outer),
            None => FormulaFnTypeLowering::new(&self.sig),
        }
    }
}

/// A spec macro's closure together with the context it was written in, the form
/// `#[thrust_macros::context]` rewrites the macro's tokens into.
pub struct ClosureWithContext {
    pub context: EnclosingContext,
    pub closure: syn::ExprClosure,
}

impl Parse for ClosureWithContext {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let context = input.parse()?;
        let closure = input.parse()?;
        Ok(Self { context, closure })
    }
}

/// A formula lifted into a `#[thrust::formula_fn]` item, with the expression naming that
/// item — generic arguments included — for the marker call to take.
pub struct LiftedFormulaFn {
    pub item: syn::ItemFn,
    pub reference: syn::Expr,
}

/// Lifts `body`, a formula over `params`, into a `#[thrust::formula_fn]` called `name`.
///
/// The parameters are lowered to their model types. The receiver `self` is renamed to
/// `__thrust_self`, which the analyzer binds back to the receiver value. Under a
/// `context`, the generics in scope there are re-declared on the item and instantiated at
/// the reference; in a method, `Self` becomes the concrete self type of the `impl`, or a
/// synthetic type parameter instantiated with the real `Self` in a trait.
pub fn lift(
    name: &syn::Ident,
    params: &[FnArg],
    body: &syn::Expr,
    context: Option<&EnclosingContext>,
) -> syn::Result<LiftedFormulaFn> {
    lift_inner(name, params, body, context, None)
}

/// [`lift`] for the formula of a statement (`proof_assert!`, `assume!`), whose parameter types may
/// leave a closure's type, which cannot be written, to the local the parameter names: a `_`
/// anywhere in a written type (`|f: _|`, `|it: &mut Filter<I, _>|`), or a type parameter of
/// `local_types`, declared before the closure (`<P: Fn(&T) -> bool> |it: &mut Filter<I, P>|`),
/// which the formula can name and whose `Fn` bound lets it use what requires one. Each becomes a
/// type parameter of the item (as a `Fn` bound would make one, so the parameter is the closure's
/// model) and the reference instantiates it with a placeholder that meets its bound, which the
/// analyzer replaces with the closure's type, matching the written type against the local's.
pub fn lift_statement(
    name: &syn::Ident,
    params: &[FnArg],
    body: &syn::Expr,
    context: Option<&EnclosingContext>,
    local_types: &syn::Generics,
) -> syn::Result<LiftedFormulaFn> {
    lift_inner(name, params, body, context, Some(local_types))
}

/// A statement's closure, with the type parameters it leaves to locals declared before it.
pub struct ClosureWithLocalTypes {
    pub local_types: syn::Generics,
    pub closure: syn::ExprClosure,
}

impl Parse for ClosureWithLocalTypes {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let local_types = if input.peek(syn::Token![<]) {
            input.parse()?
        } else {
            syn::Generics::default()
        };
        let closure = input.parse()?;
        Ok(Self {
            local_types,
            closure,
        })
    }
}

/// The prefix of the name of a type parameter left to a local; the analyzer recognizes them by
/// it (`resolve_closure_local_args`). A `_` gets the prefix and `_<n>`, a declared `P` the
/// prefix and `P`.
const ELIDED_CLOSURE_LOCAL_PREFIX: &str = "__ThrustClosureOf_";

/// A type parameter left to a local: its name in the item, its bounds, and the placeholder the
/// reference instantiates it with.
struct ClosureLocalType {
    ident: syn::Ident,
    bounds: Vec<syn::TypeParamBound>,
    placeholder: syn::Type,
}

/// The placeholder for a type parameter left to a local with `bounds`: a function pointer meets
/// an `Fn` bound, and the type `LocalType` stands where there is none.
fn closure_local_placeholder(
    ident: &syn::Ident,
    bounds: &[syn::TypeParamBound],
) -> syn::Result<syn::Type> {
    let [bound] = bounds else {
        if bounds.is_empty() {
            return Ok(syn::parse_quote!(crate::thrust_models::model::LocalType));
        }
        return Err(syn::Error::new_spanned(
            ident,
            "a type parameter left to a local takes at most one bound, `Fn`, `FnMut` or `FnOnce`",
        ));
    };
    let syn::TypeParamBound::Trait(bound) = bound else {
        return Err(syn::Error::new_spanned(
            bound,
            "expected an `Fn`, `FnMut` or `FnOnce` bound",
        ));
    };
    let segment = bound.path.segments.last().expect("a path has a segment");
    let syn::PathArguments::Parenthesized(args) = &segment.arguments else {
        return Err(syn::Error::new_spanned(
            bound,
            "expected an `Fn`, `FnMut` or `FnOnce` bound",
        ));
    };
    if !["Fn", "FnMut", "FnOnce"].iter().any(|f| segment.ident == f) {
        return Err(syn::Error::new_spanned(
            bound,
            "expected an `Fn`, `FnMut` or `FnOnce` bound",
        ));
    }
    let lifetimes = &bound.lifetimes;
    let inputs = &args.inputs;
    let output = &args.output;
    Ok(syn::parse_quote!(#lifetimes fn(#inputs) #output))
}

/// Renames the type parameters a statement declares to their names in the item.
struct LocalTypeRenamer<'a> {
    renames: &'a [(syn::Ident, syn::Ident)],
}

impl VisitMut for LocalTypeRenamer<'_> {
    fn visit_path_mut(&mut self, path: &mut syn::Path) {
        if path.leading_colon.is_none() {
            if let Some(first) = path.segments.first_mut() {
                if let Some((_, to)) = self.renames.iter().find(|(from, _)| first.ident == *from) {
                    first.ident = to.clone();
                }
            }
        }
        syn::visit_mut::visit_path_mut(self, path);
    }
}

/// `tokens` with each identifier `from` renamed to `to`.
fn rename_ident(tokens: TokenStream2, from: &syn::Ident, to: &syn::Ident) -> TokenStream2 {
    tokens
        .into_iter()
        .map(|tt| match tt {
            proc_macro2::TokenTree::Ident(ident) if ident == *from => {
                proc_macro2::TokenTree::Ident(to.clone())
            }
            proc_macro2::TokenTree::Group(group) => {
                let mut renamed = proc_macro2::Group::new(
                    group.delimiter(),
                    rename_ident(group.stream(), from, to),
                );
                renamed.set_span(group.span());
                proc_macro2::TokenTree::Group(renamed)
            }
            tt => tt,
        })
        .collect()
}

/// Replaces each `_` of a type with a fresh type parameter left to a local.
struct InferredTypeCollector<'a> {
    holes: &'a mut Vec<ClosureLocalType>,
}

impl VisitMut for InferredTypeCollector<'_> {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        if !matches!(ty, syn::Type::Infer(_)) {
            syn::visit_mut::visit_type_mut(self, ty);
            return;
        }
        let ident = format_ident!("{}_{}", ELIDED_CLOSURE_LOCAL_PREFIX, self.holes.len());
        *ty = syn::parse_quote!(#ident);
        self.holes.push(ClosureLocalType {
            ident,
            bounds: Vec::new(),
            placeholder: syn::parse_quote!(crate::thrust_models::model::LocalType),
        });
    }
}

/// The type parameters `params` and `body` leave to locals, with `local_types` renamed to their
/// names in the item and each `_` of a parameter type replaced.
fn closure_local_types(
    params: &mut [FnArg],
    body: &mut syn::Expr,
    local_types: &syn::Generics,
) -> syn::Result<Vec<ClosureLocalType>> {
    if let Some(where_clause) = &local_types.where_clause {
        return Err(syn::Error::new_spanned(
            where_clause,
            "write the bound of a type parameter left to a local in place",
        ));
    }
    let mut holes = Vec::new();
    let mut renames = Vec::new();
    for param in &local_types.params {
        let syn::GenericParam::Type(tp) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "only type parameters can be left to a local",
            ));
        };
        let ident = format_ident!("{}{}", ELIDED_CLOSURE_LOCAL_PREFIX, tp.ident);
        let bounds: Vec<syn::TypeParamBound> = tp.bounds.iter().cloned().collect();
        let placeholder = closure_local_placeholder(&tp.ident, &bounds)?;
        renames.push((tp.ident.clone(), ident.clone()));
        holes.push(ClosureLocalType {
            ident,
            bounds,
            placeholder,
        });
    }
    let mut renamer = LocalTypeRenamer { renames: &renames };
    for hole in &mut holes {
        for bound in &mut hole.bounds {
            renamer.visit_type_param_bound_mut(bound);
        }
    }
    for param in params.iter_mut() {
        renamer.visit_fn_arg_mut(param);
    }
    // The body is wrapped in `formula!(..)`, whose tokens a syntax visitor does not reach.
    let mut tokens = body.to_token_stream();
    for (from, to) in &renames {
        tokens = rename_ident(tokens, from, to);
    }
    *body = syn::parse2(tokens)?;

    for param in params.iter_mut() {
        let FnArg::Typed(pt) = param else { continue };
        let before = holes.len();
        InferredTypeCollector { holes: &mut holes }.visit_type_mut(&mut pt.ty);
        let mentions_hole = before < holes.len()
            || holes.iter().any(|hole| {
                crate::tokens_contain_ident(&pt.ty.to_token_stream(), hole.ident.to_string())
            });
        if mentions_hole && !matches!(&*pt.pat, syn::Pat::Ident(_)) {
            return Err(syn::Error::new_spanned(
                &pt.pat,
                "a parameter whose type is left to its local must be a plain variable name",
            ));
        }
    }
    Ok(holes)
}

/// [`lift`] and [`lift_statement`]; `local_types` is given by the latter.
fn lift_inner(
    name: &syn::Ident,
    params: &[FnArg],
    body: &syn::Expr,
    context: Option<&EnclosingContext>,
    local_types: Option<&syn::Generics>,
) -> syn::Result<LiftedFormulaFn> {
    let mut params = params.to_vec();
    let mut body = body.clone();
    let closure_locals = match local_types {
        Some(local_types) => closure_local_types(&mut params, &mut body, local_types)?,
        None => Vec::new(),
    };

    let mut def_params: Vec<TokenStream2> = Vec::new();
    let mut turbofish_args: Vec<TokenStream2> = Vec::new();
    for param in context
        .into_iter()
        .flat_map(EnclosingContext::generic_params)
    {
        def_params.push(param.to_token_stream());
        match param {
            GenericParam::Type(tp) => turbofish_args.push(tp.ident.to_token_stream()),
            GenericParam::Const(cp) => turbofish_args.push(cp.ident.to_token_stream()),
            GenericParam::Lifetime(_) => {}
        }
    }

    for hole in &closure_locals {
        def_params.push(hole.ident.to_token_stream());
        turbofish_args.push(hole.placeholder.to_token_stream());
    }

    let mut def_wheres: Vec<WherePredicate> = context
        .into_iter()
        .flat_map(EnclosingContext::where_predicates)
        .cloned()
        .collect();

    let dummy_sig = syn::parse_quote!(fn f());
    let mut type_lowering = match context {
        Some(context) => context.type_lowering(),
        None => FormulaFnTypeLowering::new(&dummy_sig),
    };
    type_lowering.add_closure_type_params(closure_locals.iter().map(|hole| hole.ident.clone()));

    def_wheres.extend(type_lowering.model_where_predicates());
    for hole in closure_locals.iter().filter(|hole| !hole.bounds.is_empty()) {
        let ident = &hole.ident;
        let bounds = &hole.bounds;
        def_wheres.push(syn::parse_quote!(#ident: #(#bounds)+*));
    }

    // A formula may refer to the receiver value `self`; the lifted formula function is free, so
    // rewrite `self` to a `__thrust_self` parameter. The analyzer binds it back to the receiver.
    let mut rewriter = SelfValueRewriter {
        to: format_ident!("__thrust_self"),
    };
    for param in &mut params {
        rewriter.visit_fn_arg_mut(param);
    }
    rewriter.visit_expr_mut(&mut body);

    let self_used = params
        .iter()
        .any(|param| crate::tokens_contain_ident(&param.to_token_stream(), "Self"))
        || crate::tokens_contain_ident(&body.to_token_stream(), "Self")
        || def_wheres
            .iter()
            .any(|pred| crate::tokens_contain_ident(&pred.to_token_stream(), "Self"));
    if self_used {
        let Some(outer) = context.and_then(|context| context.outer.as_ref()) else {
            return Err(syn::Error::new_spanned(
                body,
                "formula cannot refer to `Self` without an enclosing impl/trait context",
            ));
        };

        match outer {
            FnOuterItem::ItemImpl(item_impl) => {
                // `Self` in an impl method context: rewrite it to the concrete self type
                // everywhere. In a trait impl the projection `Self::Item` names the
                // implemented trait's associated item, so carry that trait along: without it
                // the substituted `<Wrap<I>>::Item` no longer says which trait to look in.
                let self_ty = &item_impl.self_ty;
                let mut rewriter = SelfTypeRewriter {
                    to: *self_ty.clone(),
                    trait_: item_impl
                        .trait_
                        .as_ref()
                        .map(|(trait_path, _)| trait_path.clone()),
                };
                for param in &mut params {
                    rewriter.visit_fn_arg_mut(param);
                }
                rewriter.visit_expr_mut(&mut body);
                for pred in &mut def_wheres {
                    rewriter.visit_where_predicate_mut(pred);
                }
            }
            FnOuterItem::ItemTrait(item_trait) => {
                // `Self` in a trait method context: rewrite it to a synthetic generic everywhere
                // it reaches the formula function — parameters, body, and the propagated
                // where-clause predicates — then pass the real `Self` via turbofish (legal
                // in expression position).
                let synth: syn::Ident = format_ident!("__ThrustSelf");
                def_wheres.push(syn::parse_quote!(#synth: ?Sized));

                let mut rewriter = SelfTypeRewriter {
                    to: syn::parse_quote!(#synth),
                    // `#synth` is a type parameter bound by the trait below, so
                    // `<#synth>::Item` resolves through that bound on its own.
                    trait_: None,
                };
                for param in &mut params {
                    rewriter.visit_fn_arg_mut(param);
                }
                rewriter.visit_expr_mut(&mut body);
                for pred in &mut def_wheres {
                    rewriter.visit_where_predicate_mut(pred);
                }
                def_params.push(quote!(#synth));
                def_wheres.extend(type_lowering.model_where_predicates_for(&synth));

                // Mirror the host's implicit `Self: Trait` bound onto the synthetic
                // generic so trait associated types (`Self::Item`) and predicates
                // (`Self::step`) remain resolvable on it.
                let trait_ident = &item_trait.ident;
                let (_, ty_generics, _) = item_trait.generics.split_for_impl();
                def_wheres.push(syn::parse_quote!(#synth: #trait_ident #ty_generics));

                turbofish_args.push(quote!(Self));

                // Rewriting `Self` to the synthetic generic can yield predicates that
                // duplicate the synthetic generic's own `Model` bounds; drop the dups.
                let mut seen = std::collections::HashSet::new();
                def_wheres.retain(|pred| seen.insert(pred.to_token_stream().to_string()));
            }
        }
    }

    let model_ty_params = type_lowering.lower_params(&params);

    let def_generics = if def_params.is_empty() {
        quote!()
    } else {
        quote!(<#(#def_params),*>)
    };
    let where_clause = if def_wheres.is_empty() {
        quote!()
    } else {
        quote!(where #(#def_wheres),*)
    };
    let turbofish = if turbofish_args.is_empty() {
        quote!()
    } else {
        quote!(::<#(#turbofish_args),*>)
    };

    Ok(LiftedFormulaFn {
        item: syn::parse_quote!(
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[allow(non_camel_case_types)]
            #[thrust::formula_fn]
            fn #name #def_generics(#model_ty_params) -> bool #where_clause {
                #body
            }
        ),
        reference: syn::parse_quote!(#name #turbofish),
    })
}

struct SelfValueRewriter {
    to: syn::Ident,
}

impl VisitMut for SelfValueRewriter {
    fn visit_pat_ident_mut(&mut self, pat: &mut syn::PatIdent) {
        if pat.ident == "self" {
            pat.ident = self.to.clone();
        }
        syn::visit_mut::visit_pat_ident_mut(self, pat);
    }

    fn visit_fn_arg_mut(&mut self, arg: &mut syn::FnArg) {
        match arg {
            syn::FnArg::Receiver(receiver) => {
                let to = &self.to;
                let ty = crate::receiver_type(receiver);
                *arg = syn::parse_quote!(#to: #ty);
            }
            syn::FnArg::Typed(_) => { /* handled by visit_pat_ident_mut */ }
        }

        syn::visit_mut::visit_fn_arg_mut(self, arg);
    }

    fn visit_expr_path_mut(&mut self, expr_path: &mut syn::ExprPath) {
        if expr_path.qself.is_some() {
            syn::visit_mut::visit_expr_path_mut(self, expr_path);
            return;
        }

        if expr_path.path.leading_colon.is_some() || expr_path.path.segments.len() != 1 {
            syn::visit_mut::visit_expr_path_mut(self, expr_path);
            return;
        }

        if expr_path.path.segments[0].ident == "self" {
            expr_path.path.segments[0].ident = self.to.clone();
            return;
        }

        syn::visit_mut::visit_expr_path_mut(self, expr_path);
    }

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if !is_formula_macro(&mac.path) {
            syn::visit_mut::visit_macro_mut(self, mac);
            return;
        }

        let expanded = crate::formula::expand(mac.tokens.clone());
        let Ok(mut expr) = syn::parse2::<syn::Expr>(expanded) else {
            return;
        };
        self.visit_expr_mut(&mut expr);
        mac.tokens = expr.into_token_stream();
    }
}

struct SelfTypeRewriter {
    to: syn::Type,
    /// The trait an enclosing `impl` implements, used to qualify a `Self::Assoc`
    /// projection as `<#to as #trait_>::Assoc`.
    trait_: Option<syn::Path>,
}

impl VisitMut for SelfTypeRewriter {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        syn::visit_mut::visit_type_mut(self, ty);

        let syn::Type::Path(type_path) = ty else {
            return;
        };

        if type_path.qself.is_some() || type_path.path.leading_colon.is_some() {
            return;
        }

        let mut segments = type_path.path.segments.iter();

        if segments.next().is_none_or(|first| first.ident != "Self") {
            return;
        }

        let tail: syn::punctuated::Punctuated<_, syn::Token![::]> = segments.cloned().collect();

        if tail.is_empty() {
            *ty = self.to.clone();
        } else {
            let to = &self.to;
            *ty = match &self.trait_ {
                Some(trait_) => syn::parse_quote!(<#to as #trait_>::#tail),
                None => syn::parse_quote!(<#to>::#tail),
            }
        };
    }

    fn visit_expr_path_mut(&mut self, expr_path: &mut syn::ExprPath) {
        syn::visit_mut::visit_expr_path_mut(self, expr_path);

        if expr_path.qself.is_some() || expr_path.path.leading_colon.is_some() {
            return;
        }

        let mut segments = expr_path.path.segments.iter();

        if segments.next().is_none_or(|first| first.ident != "Self") {
            return;
        }

        let tail: syn::punctuated::Punctuated<_, syn::Token![::]> = segments.cloned().collect();

        if tail.is_empty() {
            return;
        }

        let to = &self.to;
        *expr_path = syn::parse_quote!(<#to>::#tail);
    }

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if !is_formula_macro(&mac.path) {
            syn::visit_mut::visit_macro_mut(self, mac);
            return;
        }

        let expanded = crate::formula::expand(mac.tokens.clone());
        let Ok(mut expr) = syn::parse2::<syn::Expr>(expanded) else {
            return;
        };
        self.visit_expr_mut(&mut expr);
        mac.tokens = expr.into_token_stream();
    }
}

fn is_formula_macro(path: &syn::Path) -> bool {
    // TODO: identify the macro precisely
    path.segments
        .last()
        .is_some_and(|seg| seg.ident == "formula")
}
