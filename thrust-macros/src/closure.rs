//! Expansion of `thrust_macros::closure!`, which attaches an explicit
//! `requires`/`ensures` specification to a closure expression.
//!
//! ```ignore
//! let f = thrust_macros::closure!(
//!     captures(n: i32),
//!     requires(x > 0),
//!     ensures(result > x + n),
//!     |x: i32| -> i32 { x + n + 1 },
//! );
//! ```
//!
//! Rust attributes cannot sit on a closure expression, so the clauses are written
//! inside the macro. The expansion prepends `#[thrust::formula_fn]` companions and
//! `#[thrust::requires_path]` / `#[thrust::ensures_path]` path statements to the
//! closure body — the markers the plugin already reads for named `fn` specs (see
//! `spec.rs`). Each clause is optional (an omitted one leaves that side inferred)
//! and may be repeated, in which case its predicates are conjoined.
//!
//! `captures` restates the captured variables a clause wants to name, with the types
//! they are captured by the closure. Only the ones a clause names need restating, and
//! in any order: the plugin matches them against the closure's real captures by name.
//!
//! `unnest` gives the relation `unnest!` holds between two states of an `FnMut` closure, in
//! place of the one derived from its captures, which says nothing of a capture taken by value.
//! It reads a capture `x` as `*x` at the first state and `!x` at the second, as `ensures` reads
//! the receiver's current and final state. The analyzer checks it reflexive and transitive,
//! and each call's postcondition includes it.
//!
//! Under `#[thrust_macros::context]` a clause sees the enclosing function's generics, so a
//! closure in a generic function can name generic-typed captures; without it a clause sees no
//! generic or `Self` context.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    FnArg,
};

use crate::formula_fn_lifting::{self, EnclosingContext, LiftedFormulaFn};
use crate::FormulaFnTypeLowering;

mod kw {
    syn::custom_keyword!(captures);
    syn::custom_keyword!(requires);
    syn::custom_keyword!(ensures);
    syn::custom_keyword!(unnest);
}

struct ClosureSpec {
    captures: Vec<FnArg>,
    requires: Vec<TokenStream2>,
    ensures: Vec<TokenStream2>,
    unnest: Vec<TokenStream2>,
    closure: syn::ExprClosure,
}

impl Parse for ClosureSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut captures = Vec::new();
        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        let mut unnest = Vec::new();

        loop {
            if input.peek(kw::captures) {
                input.parse::<kw::captures>()?;
                let content;
                parenthesized!(content in input);
                captures.extend(content.parse_terminated(FnArg::parse, syn::Token![,])?);
            } else {
                let clause = if input.peek(kw::requires) {
                    input.parse::<kw::requires>()?;
                    &mut requires
                } else if input.peek(kw::ensures) {
                    input.parse::<kw::ensures>()?;
                    &mut ensures
                } else if input.peek(kw::unnest) {
                    input.parse::<kw::unnest>()?;
                    &mut unnest
                } else {
                    break;
                };
                let content;
                parenthesized!(content in input);
                clause.push(content.parse()?);
            }
            input.parse::<Option<syn::Token![,]>>()?;
        }

        let closure: syn::ExprClosure = input.parse()?;
        input.parse::<Option<syn::Token![,]>>()?;

        Ok(Self {
            captures,
            requires,
            ensures,
            unnest,
            closure,
        })
    }
}

pub fn expand(input: TokenStream) -> TokenStream {
    let spec = match syn::parse::<ClosureSpec>(input) {
        Ok(spec) => spec,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_closure(spec, None) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// A `closure!` with the enclosing context `#[thrust_macros::context]` threads in.
struct ClosureSpecWithContext {
    context: EnclosingContext,
    spec: ClosureSpec,
}

impl Parse for ClosureSpecWithContext {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let context = input.parse()?;
        let spec = input.parse()?;
        Ok(Self { context, spec })
    }
}

/// Expands `_closure_with_context!(#outer_attr #sig; SPEC)`, the form
/// `#[thrust_macros::context]` rewrites each `closure!` into.
pub fn expand_with_context(input: TokenStream) -> TokenStream {
    let ClosureSpecWithContext { context, spec } = match syn::parse(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_closure(spec, Some(&context)) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn expand_closure(
    spec: ClosureSpec,
    context: Option<&EnclosingContext>,
) -> syn::Result<syn::ExprClosure> {
    let ClosureSpec {
        captures,
        requires,
        ensures,
        unnest,
        mut closure,
    } = spec;

    let upvars = upvars_param(&captures)?;
    let mut arg_params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "closure! requires explicitly typed closure parameters, e.g. `|x: i32| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        arg_params.push(syn::parse_quote!(#pat: #ty));
    }

    if !ensures.is_empty() && matches!(closure.output, syn::ReturnType::Default) {
        return Err(syn::Error::new_spanned(
            &closure,
            "closure! with `ensures` requires an explicit return type, e.g. `|x: i32| -> i32 { .. }`",
        ));
    }

    if let Some(context) = context {
        let prelude = context_companions(
            context,
            &upvars,
            &arg_params,
            &closure.output,
            [requires, ensures, unnest],
        )?;
        splice_prelude(&mut closure, prelude);
        return Ok(closure);
    }

    // The lowering reads generics off a signature to spot `Fn`-bounded type params; a
    // clause has none of its own.
    let spec_sig: syn::Signature = syn::parse_quote!(fn closure_spec());
    let type_lowering = FormulaFnTypeLowering::new(&spec_sig);
    // A closure's parameters are `[upvars, arg1, .., argN]`. The companions take the
    // upvars in that same leading position, so their parameters line up with the
    // closure's.
    let upvars_model = type_lowering.lower_params([&upvars]);
    let arg_models = type_lowering.lower_params(&arg_params);

    let mut prelude: Vec<TokenStream2> = Vec::new();
    if let Some(body) = conjoin(requires) {
        prelude.push(quote! {
            #[allow(unused_variables, non_snake_case)]
            #[thrust::formula_fn]
            fn _thrust_closure_requires(
                #[thrust::closure_upvars] #upvars_model,
                #arg_models
            ) -> bool {
                #body
            }

            #[thrust::requires_path]
            _thrust_closure_requires;
        });
    }
    if let Some(body) = conjoin(ensures) {
        let ret_model = type_lowering.lower_return_type(&closure.output);
        prelude.push(quote! {
            #[allow(unused_variables, non_snake_case)]
            #[thrust::formula_fn]
            fn _thrust_closure_ensures(
                result: #ret_model,
                #[thrust::closure_upvars] #upvars_model,
                #arg_models
            ) -> bool {
                #body
            }

            #[thrust::ensures_path]
            _thrust_closure_ensures;
        });
    }
    if let Some(body) = conjoin(unnest) {
        prelude.push(quote! {
            #[allow(unused_variables, non_snake_case)]
            #[thrust::formula_fn]
            fn _thrust_closure_unnest(
                #[thrust::closure_upvars] #upvars_model
            ) -> bool {
                #body
            }

            #[thrust::unnest_path]
            _thrust_closure_unnest;
        });
    }

    splice_prelude(&mut closure, prelude);
    Ok(closure)
}

/// The companions of the clauses `[requires, ensures, unnest]` lifted with the enclosing
/// generics, each referred to with them as arguments.
fn context_companions(
    context: &EnclosingContext,
    upvars: &FnArg,
    arg_params: &[FnArg],
    output: &syn::ReturnType,
    [requires, ensures, unnest]: [Vec<TokenStream2>; 3],
) -> syn::Result<Vec<TokenStream2>> {
    let upvars: FnArg = {
        let FnArg::Typed(pt) = upvars else {
            unreachable!("upvars_param builds a typed parameter");
        };
        let (pat, ty) = (&pt.pat, &pt.ty);
        syn::parse_quote!(#[thrust::closure_upvars] #pat: #ty)
    };
    let mut prelude = Vec::new();
    let mut lift = |name: &str, params: Vec<FnArg>, body: TokenStream2, marker: TokenStream2| {
        let name = quote::format_ident!("{}", name);
        let body: syn::Expr = syn::parse2(body)?;
        let LiftedFormulaFn { item, reference } =
            formula_fn_lifting::lift(&name, &params, &body, Some(context))?;
        prelude.push(quote! {
            #item

            #marker
            #reference;
        });
        syn::Result::Ok(())
    };
    if let Some(body) = conjoin(requires) {
        let params = std::iter::once(upvars.clone())
            .chain(arg_params.iter().cloned())
            .collect();
        lift(
            "_thrust_closure_requires",
            params,
            body,
            quote!(#[thrust::requires_path]),
        )?;
    }
    if let Some(body) = conjoin(ensures) {
        let syn::ReturnType::Type(_, ret) = output else {
            unreachable!("checked above: `ensures` needs an explicit return type");
        };
        let result: FnArg = syn::parse_quote!(result: #ret);
        let params = [result, upvars.clone()]
            .into_iter()
            .chain(arg_params.iter().cloned())
            .collect();
        lift(
            "_thrust_closure_ensures",
            params,
            body,
            quote!(#[thrust::ensures_path]),
        )?;
    }
    if let Some(body) = conjoin(unnest) {
        lift(
            "_thrust_closure_unnest",
            vec![upvars],
            body,
            quote!(#[thrust::unnest_path]),
        )?;
    }
    Ok(prelude)
}

fn splice_prelude(closure: &mut syn::ExprClosure, prelude: Vec<TokenStream2>) {
    // Splice into the body's own block rather than nesting it inside a new one, which
    // would warn `unused_braces`. A block carrying a label or attributes has to stay
    // whole, so it becomes the tail expression of the new block instead.
    let body_stmts = match *closure.body {
        syn::Expr::Block(ref block) if block.attrs.is_empty() && block.label.is_none() => {
            block.block.stmts.clone()
        }
        ref body => vec![syn::Stmt::Expr(body.clone(), None)],
    };
    closure.body = Box::new(syn::parse_quote!({
        #(#prelude)*
        #(#body_stmts)*
    }));
}

/// The companion parameter holding the closure's upvars: a tuple of the captures a
/// clause names, which the plugin matches up with the real upvars by name.
fn upvars_param(captures: &[FnArg]) -> syn::Result<FnArg> {
    let mut names = Vec::new();
    let mut tys = Vec::new();
    for capture in captures {
        let FnArg::Typed(capture) = capture else {
            return Err(syn::Error::new_spanned(
                capture,
                "closure! captures are written as `name: Type`",
            ));
        };
        names.push(&capture.pat);
        tys.push(&capture.ty);
    }
    Ok(syn::parse_quote!((#(#names,)*): (#(#tys,)*)))
}

fn conjoin(preds: Vec<TokenStream2>) -> Option<TokenStream2> {
    preds
        .into_iter()
        .map(|pred| {
            let pred = crate::formula::expand(pred);
            quote!((#pred))
        })
        .reduce(|acc, pred| quote!(#acc && #pred))
}
