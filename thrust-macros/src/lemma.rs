//! Expansion of `#[thrust_macros::lemma]` and `thrust_macros::proof!`.
//!
//! A lemma is an ordinary function whose contract is the statement and whose body is the proof.
//! With `#[thrust_macros::variant(e)]`, each call the body makes to the lemma itself is redirected
//! to a companion `_thrust_lemma_rec_<name>`, which has the lemma's contract. The companion
//! names the variant as a logic function of all the lemma's parameters
//! (`_thrust_lemma_variant_<name>`). The analyzer proves at each call in the lemma's own body that
//! the variant is non-negative at the parameters' values on entry and smaller at the call's
//! arguments than there (`analyze::basic_block`); it checks the rest of what makes a lemma
//! terminate (`analyze::lemma`).

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::visit_mut::VisitMut;

use crate::formula_fn_type_lowering::FormulaFnTypeLowering;
use crate::spec::{generic_params_tokens, generic_turbofish, has_last_segment, take_variant};

pub fn expand(item: TokenStream) -> TokenStream {
    let mut func = syn::parse_macro_input!(item as syn::ItemFn);
    // The parameters its contract (and its variant) mentions are read by it, whatever the body
    // reads.
    let attrs = func.attrs.clone();
    crate::spec::allow_unused_contract_params(&attrs, &mut func.sig.inputs, false);
    let variant = match take_variant(&mut func.attrs) {
        Ok(variant) => variant,
        Err(e) => return error_with(e, &func),
    };
    func.attrs.push(syn::parse_quote!(#[thrust::lemma]));
    // A lemma is a statement the program uses only through `proof!`.
    func.attrs.push(syn::parse_quote!(#[allow(dead_code)]));
    let Some(variant) = variant else {
        return func.into_token_stream().into();
    };
    match expand_recursive(func.clone(), variant) {
        Ok(tokens) => tokens.into(),
        Err(e) => error_with(e, &func),
    }
}

fn error_with(e: syn::Error, func: &syn::ItemFn) -> TokenStream {
    let err = e.to_compile_error();
    quote! { #err #func }.into()
}

fn expand_recursive(mut func: syn::ItemFn, variant: TokenStream2) -> syn::Result<TokenStream2> {
    let params = typed_params(&func.sig)?;
    let name = func.sig.ident.clone();
    let rec_name = format_ident!("_thrust_lemma_rec_{}", name);
    let variant_name = format_ident!("_thrust_lemma_variant_{}", name);
    let wrapper_name = format_ident!("_thrust_lemma_variant_of_{}", name);
    let variant_fn = variant_fn(&variant_name, &func.sig, variant);
    let wrapper = variant_wrapper(&wrapper_name, &variant_name, &rec_name, &func.sig);

    RedirectSelfCalls {
        name: &name,
        rec_name: &rec_name,
    }
    .visit_block_mut(&mut func.block);

    let contract = func.attrs.iter().filter(|attr| {
        ["requires", "ensures", "_requires_ensures"]
            .iter()
            .any(|name| has_last_segment(attr, name))
    });
    let generics = generic_params_tokens(&func.sig.generics);
    let turbofish = generic_turbofish(&func.sig.generics);
    let where_clause = &func.sig.generics.where_clause;
    let output = &func.sig.output;
    let call_params = params.iter().map(|(param, ty)| quote!(#param: #ty));
    let call_args = params.iter().map(|(param, _)| param);
    Ok(quote! {
        #func

        #variant_fn
        #wrapper

        #(#contract)*
        #[thrust::lemma_rec]
        #[allow(dead_code, non_snake_case, unused_variables, path_statements)]
        fn #rec_name #generics(#(#call_params),*) #output #where_clause {
            #name #turbofish(#(#call_args),*)
        }
    })
}

/// What ties the companion to its variant: a function with the variant's `Model` bounds, as the
/// extern specification a contract makes has them, naming the companion and the variant's logic
/// function at the lemma's generics. The companion itself has only the lemma's bounds, which the
/// lemma's own body satisfies, so it cannot name the variant.
fn variant_wrapper(
    name: &syn::Ident,
    variant_name: &syn::Ident,
    rec_name: &syn::Ident,
    sig: &syn::Signature,
) -> TokenStream2 {
    let generics = generic_params_tokens(&sig.generics);
    let turbofish = generic_turbofish(&sig.generics);
    let where_clause = variant_where_clause(sig);
    quote! {
        #[allow(dead_code, non_snake_case, path_statements)]
        #[thrust::lemma_variant_wrapper]
        fn #name #generics() #where_clause {
            #[thrust::lemma_variant_obligation]
            #variant_name #turbofish;
            #[thrust::lemma_variant_companion]
            #rec_name #turbofish;
        }
    }
}

/// The lemma's own predicates and the `Model` bounds of its types.
fn variant_where_clause(sig: &syn::Signature) -> TokenStream2 {
    let model_preds = FormulaFnTypeLowering::new(sig).model_where_predicates();
    let existing = sig
        .generics
        .where_clause
        .iter()
        .flat_map(|clause| clause.predicates.iter());
    quote!(where #(#existing,)* #(#model_preds),*)
}

/// The variant as a logic function of all the lemma's parameters, with the lemma's generics, as
/// for a recursive logic function (`spec::expand_spec_fn`). The analyzer instantiates it at the
/// parameters' values on entry and at a recursive call's arguments (`analyze::basic_block`), so
/// rustc resolves the variant's names, binders and macros.
fn variant_fn(name: &syn::Ident, sig: &syn::Signature, variant: TokenStream2) -> TokenStream2 {
    let generics = generic_params_tokens(&sig.generics);
    let type_lowering = FormulaFnTypeLowering::new(sig);
    let model_params = type_lowering.lower_params(&sig.inputs);
    let where_clause = variant_where_clause(sig);
    let variant = crate::formula::expand(variant);
    quote! {
        #[allow(dead_code, unused_variables, non_snake_case)]
        #[thrust::formula_fn]
        #[thrust::logic]
        fn #name #generics(#model_params)
            -> impl crate::thrust_models::Model<Ty: crate::thrust_models::model::Integer>
            #where_clause
        {
            #variant
        }
    }
}

/// The parameters of a lemma with a variant, which are all named by an identifier.
fn typed_params(sig: &syn::Signature) -> syn::Result<Vec<(syn::Ident, syn::Type)>> {
    sig.inputs
        .iter()
        .map(|input| match input {
            syn::FnArg::Typed(syn::PatType { pat, ty, .. }) => match &**pat {
                syn::Pat::Ident(pat) if pat.subpat.is_none() => {
                    Ok((pat.ident.clone(), (**ty).clone()))
                }
                _ => Err(syn::Error::new_spanned(
                    pat,
                    "a parameter of a lemma with a variant is a plain identifier",
                )),
            },
            syn::FnArg::Receiver(receiver) => Err(syn::Error::new_spanned(
                receiver,
                "a lemma with a variant is a free function",
            )),
        })
        .collect()
}

/// Redirects each call `name(args)` to the companion, `rec_name(args)`. Thrust proves, at each
/// call of the companion in the lemma's own body, that the variant decreases
/// (`analyze::basic_block`); the redirected path has the span of the expansion, so that a call
/// the user writes to the companion itself is told apart.
struct RedirectSelfCalls<'a> {
    name: &'a syn::Ident,
    rec_name: &'a syn::Ident,
}

impl VisitMut for RedirectSelfCalls<'_> {
    fn visit_expr_call_mut(&mut self, call: &mut syn::ExprCall) {
        syn::visit_mut::visit_expr_call_mut(self, call);
        let syn::Expr::Path(func) = &mut *call.func else {
            return;
        };
        let Some(last) = func.path.segments.last_mut() else {
            return;
        };
        if last.ident != *self.name {
            return;
        }
        last.ident = syn::Ident::new(&self.rec_name.to_string(), proc_macro2::Span::call_site());
    }
}

/// `proof!(lemma(args))`: the arguments are evaluated, and the call is made in a branch the
/// analysis takes and the program does not.
pub fn expand_proof(input: TokenStream) -> TokenStream {
    let call = syn::parse_macro_input!(input as syn::ExprCall);
    let func = &call.func;
    let args: Vec<syn::Ident> = (0..call.args.len())
        .map(|i| format_ident!("__thrust_proof_arg{}", i))
        .collect();
    let values = call.args.iter();
    quote! {{
        #(
            #[allow(unused_variables)]
            let #args = #values;
        )*
        if crate::thrust_models::__proof_branch() {
            #func(#(#args),*);
        }
    }}
    .into()
}
