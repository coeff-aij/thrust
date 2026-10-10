//! Expansion of `#[thrust_macros::lemma]` and `thrust_macros::proof!`.
//!
//! A lemma is an ordinary function whose contract is the statement and whose body is the proof.
//! With `#[thrust_macros::variant(e)]`, each call the body makes to the lemma itself is redirected
//! to a companion `_thrust_lemma_rec_<name>`, which takes the entry values of the parameters as
//! well and requires `e` to be non-negative there and smaller at the call's arguments. The
//! analyzer checks the rest of what makes a lemma terminate (`analyze::lemma`).

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::visit_mut::VisitMut;

use crate::spec::{generic_params_tokens, generic_turbofish, has_last_segment, take_variant};

pub fn expand(item: TokenStream) -> TokenStream {
    let mut func = syn::parse_macro_input!(item as syn::ItemFn);
    let variant = match take_variant(&mut func.attrs) {
        Ok(variant) => variant,
        Err(e) => return error_with(e, &func),
    };
    func.attrs.push(syn::parse_quote!(#[thrust::lemma]));
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
    let entries: Vec<syn::Ident> = params
        .iter()
        .map(|(param, _)| format_ident!("__thrust_entry_{}", param))
        .collect();

    RedirectSelfCalls {
        name: &name,
        rec_name: &rec_name,
        entries: &entries,
    }
    .visit_block_mut(&mut func.block);
    let param_idents = params.iter().map(|(param, _)| param);
    let stmts = &func.block.stmts;
    func.block = syn::parse_quote!({
        #(
            #[allow(unused_variables)]
            let #entries = &#param_idents;
        )*
        #(#stmts)*
    });

    let variant: syn::Expr = syn::parse2(variant)?;
    let mut variant_at_entry = variant.clone();
    SubstEntries {
        params: &params,
        entries: &entries,
    }
    .visit_expr_mut(&mut variant_at_entry);

    let contract = func.attrs.iter().filter(|attr| {
        ["requires", "ensures", "_requires_ensures"]
            .iter()
            .any(|name| has_last_segment(attr, name))
    });
    let generics = generic_params_tokens(&func.sig.generics);
    let turbofish = generic_turbofish(&func.sig.generics);
    let where_clause = &func.sig.generics.where_clause;
    let output = &func.sig.output;
    let entry_params = entries
        .iter()
        .zip(&params)
        .map(|(entry, (_, ty))| quote!(#entry: &#ty));
    let call_params = params.iter().map(|(param, ty)| quote!(#param: #ty));
    let call_args = params.iter().map(|(param, _)| param);
    Ok(quote! {
        #func

        #(#contract)*
        #[::thrust_macros::requires((#variant_at_entry) >= 0 && (#variant) < (#variant_at_entry))]
        #[thrust::lemma_rec]
        #[allow(dead_code, non_snake_case, unused_variables)]
        fn #rec_name #generics(#(#entry_params,)* #(#call_params),*) #output #where_clause {
            #name #turbofish(#(#call_args),*)
        }
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

/// Rewrites each call `name(args)` into `rec_name(entries.., args)`.
struct RedirectSelfCalls<'a> {
    name: &'a syn::Ident,
    rec_name: &'a syn::Ident,
    entries: &'a [syn::Ident],
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
        last.ident = self.rec_name.clone();
        let args = std::mem::take(&mut call.args);
        let entries = self.entries;
        call.args = syn::parse_quote!(#(#entries,)* #args);
    }
}

/// Replaces each parameter in a variant by its value on entry, `(*__thrust_entry_<param>)`.
struct SubstEntries<'a> {
    params: &'a [(syn::Ident, syn::Type)],
    entries: &'a [syn::Ident],
}

impl VisitMut for SubstEntries<'_> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if let syn::Expr::Path(path) = expr {
            if let Some(ident) = path.path.get_ident() {
                if let Some(i) = self.params.iter().position(|(param, _)| param == ident) {
                    let entry = &self.entries[i];
                    *expr = syn::parse_quote!((*#entry));
                    return;
                }
            }
        }
        syn::visit_mut::visit_expr_mut(self, expr);
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
