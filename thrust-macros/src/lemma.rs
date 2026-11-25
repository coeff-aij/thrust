//! Expansion of `#[thrust_macros::lemma]` and `thrust_macros::proof!`.
//!
//! A lemma is an ordinary function whose contract is the statement and whose body is the proof.
//! With `#[thrust_macros::variant(e)]`, each call the body makes to the lemma itself is redirected
//! to a companion `_thrust_lemma_rec_<name>`, which has the lemma's contract. The companion
//! carries the formula that `e` is non-negative at the call's arguments and smaller there than at
//! the parameters' values on entry, which the analyzer proves at each call in the lemma's own body
//! (`analyze::basic_block`); it checks the rest of what makes a lemma terminate (`analyze::lemma`).

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::visit_mut::VisitMut;

use crate::formula_fn_lifting::LiftedFormulaFn;
use crate::invariant::lift_statement_closure;
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
    let variant: syn::Expr = syn::parse2(variant)?;
    let obligation = variant_obligation(&params, &variant)?;

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
    let LiftedFormulaFn { item, reference } = obligation;
    Ok(quote! {
        #func

        #(#contract)*
        #[thrust::lemma_rec]
        #[allow(dead_code, non_snake_case, unused_variables, path_statements)]
        fn #rec_name #generics(#(#call_params),*) #output #where_clause {
            #item
            #[thrust::lemma_variant_path]
            #reference;
            #name #turbofish(#(#call_args),*)
        }
    })
}

/// The formula a call of the lemma in its own body has to prove, as a formula function over the
/// parameters that the variant reads, at the call's arguments, and `old!(p)`, the value `p` had
/// on entry: the variant at the arguments is non-negative and smaller than at the parameters on
/// entry. Thrust gives the entry values itself; no code of the lemma supplies them.
fn variant_obligation(
    params: &[(syn::Ident, syn::Type)],
    variant: &syn::Expr,
) -> syn::Result<LiftedFormulaFn> {
    let mut read = Reads {
        params,
        names: Vec::new(),
    };
    read.visit_expr_mut(&mut variant.clone());
    let at_args = variant;
    let mut at_entry = variant.clone();
    EntryValues { params }.visit_expr_mut(&mut at_entry);
    let args = read.names.iter().map(|&i| {
        let (param, ty) = &params[i];
        quote!(#param: #ty)
    });
    let entries = read.names.iter().map(|&i| {
        let (param, ty) = &params[i];
        quote!(old!(#param): #ty)
    });
    lift_statement_closure(quote! {
        |#(#args,)* #(#entries),*| (#at_entry) >= 0 && (#at_args) < (#at_entry)
    })
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

/// The indices of the parameters a variant reads.
struct Reads<'a> {
    params: &'a [(syn::Ident, syn::Type)],
    names: Vec<usize>,
}

impl VisitMut for Reads<'_> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let Some(i) = param_index(self.params, expr) {
            if !self.names.contains(&i) {
                self.names.push(i);
            }
            return;
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

/// Replaces each parameter a variant reads by `old!(param)`.
struct EntryValues<'a> {
    params: &'a [(syn::Ident, syn::Type)],
}

impl VisitMut for EntryValues<'_> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let Some(i) = param_index(self.params, expr) {
            let param = &self.params[i].0;
            *expr = syn::parse_quote!(old!(#param));
            return;
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }
}

/// The index of the parameter `expr` names, if it is one.
fn param_index(params: &[(syn::Ident, syn::Type)], expr: &syn::Expr) -> Option<usize> {
    let syn::Expr::Path(path) = expr else {
        return None;
    };
    let ident = path.path.get_ident()?;
    params.iter().position(|(param, _)| param == ident)
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
