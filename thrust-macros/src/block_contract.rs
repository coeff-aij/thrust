//! Expansion of `thrust_macros::block_contract!`, a contract on a block written as the function
//! the block would be extracted into, with the body executed in place:
//!
//! ```ignore
//! block_contract!(
//!     |a1: T1, mut a2: T2, a3: &mut T3| -> R
//!     requires(REQUIRES),
//!     ensures(ENSURES),
//!     { BODY }
//! )
//! ```
//!
//! The body runs in place between two markers that name the extracted function, and the analysis
//! reads the region as a call of it. The function has exactly that signature and contract and is
//! generated from the same text; the block is verified as if it were extracted into it. Its
//! parameters take the outer variables with their own types, which the type check of a call that
//! never runs ensures. A parameter written `mut` may be changed by the body, and the function
//! returns its final value after the result (a `&mut` parameter is the exception: it is passed as
//! in a call, written through only when written `mut`, and a `&mut` parameter not written `mut`
//! gets `!p == *p` in `ensures`, which the check of the body proves), so that `ensures` names the final value as `x`, the
//! entry value as `old!(x)` and the result as `result`, as in a function with `&mut`. A `return`,
//! `?` or `break` that leaves the block is an error that the analysis reports.
//!
//! Without `#[thrust_macros::context]` the function is nested at the block, which cannot use the
//! enclosing function's generics. Under it the function is hoisted next to the enclosing
//! function, with that function's generic parameters and where clause, and called by path (see
//! [`Hoisted`]).

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro2::TokenStream;
use quote::{format_ident, quote, quote_spanned};
use syn::parse::{Parse, ParseStream};

mod kw {
    syn::custom_keyword!(requires);
    syn::custom_keyword!(ensures);
}

/// The parsed form: the parameters, the result type, the contract and the block.
pub struct BlockContract {
    /// The type parameters the block declares, `<P: Bound>`, that its parameters' types and its
    /// contract name; they are generics of the extracted function.
    generics: syn::Generics,
    params: Vec<Param>,
    output: syn::ReturnType,
    requires: Vec<TokenStream>,
    ensures: Vec<TokenStream>,
    body: syn::Block,
}

/// A parameter: `mut? name: ty`, or `mut? name` for a parameter whose type is the outer
/// variable's, whatever it is: the extracted function takes it as a type parameter of its own
/// (`__T<i>`, without bounds) that the call instantiates at the variable's type.
struct Param {
    pat: syn::PatIdent,
    ty: syn::Type,
    /// Whether `ty` is the type parameter generated for a parameter written without a type.
    is_generated: bool,
}

/// The type parameter of the extracted function for the untyped parameter `index`.
fn generated_type(index: usize) -> syn::Type {
    let ident = format_ident!("__T{index}");
    syn::parse_quote!(#ident)
}

impl Param {
    /// Whether the type is written `&mut T`: such a parameter is passed as a call argument, its
    /// final value kept by the caller, and is not returned in-out.
    fn is_mut_ref(&self) -> bool {
        matches!(&self.ty, syn::Type::Reference(reference) if reference.mutability.is_some())
    }
}

impl Parse for Param {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let syn::Pat::Ident(pat) = syn::Pat::parse_single(input)? else {
            return Err(
                input.error("a parameter is a name: it takes the outer variable of that name")
            );
        };
        if pat.by_ref.is_some() || pat.subpat.is_some() {
            return Err(syn::Error::new_spanned(
                pat,
                "a parameter is a name: it takes the outer variable of that name",
            ));
        }
        if input.peek(syn::Token![:]) {
            input.parse::<syn::Token![:]>()?;
            return Ok(Param {
                pat,
                ty: input.parse()?,
                is_generated: false,
            });
        }
        // the index is set once the parameters are collected
        Ok(Param {
            pat,
            ty: generated_type(0),
            is_generated: true,
        })
    }
}

fn clause<K: Parse>(input: ParseStream) -> syn::Result<TokenStream> {
    input.parse::<K>()?;
    let content;
    syn::parenthesized!(content in input);
    content.parse()
}

impl BlockContract {
    /// The form written as `tokens`.
    pub fn parse_tokens(tokens: TokenStream) -> syn::Result<Self> {
        syn::parse::Parser::parse2(|input: ParseStream| Self::parse_in(input), tokens)
    }

    fn parse_in(input: ParseStream) -> syn::Result<Self> {
        let generics = match input.peek(syn::Token![<]) {
            true => input.parse()?,
            false => syn::Generics::default(),
        };
        input.parse::<syn::Token![|]>()?;
        let mut params: Vec<Param> = Vec::new();
        while !input.peek(syn::Token![|]) {
            let mut param: Param = input.parse()?;
            if param.is_generated {
                param.ty = generated_type(params.len());
            }
            params.push(param);
            if input.peek(syn::Token![,]) {
                input.parse::<syn::Token![,]>()?;
            }
        }
        input.parse::<syn::Token![|]>()?;
        let output = input.parse()?;

        let mut requires = Vec::new();
        let mut ensures = Vec::new();
        loop {
            if input.peek(kw::requires) {
                requires.push(clause::<kw::requires>(input)?);
            } else if input.peek(kw::ensures) {
                ensures.push(clause::<kw::ensures>(input)?);
            } else {
                break;
            }
            input.parse::<syn::Token![,]>()?;
        }
        let body = input.parse()?;
        input.parse::<Option<syn::Token![,]>>()?;
        Ok(BlockContract {
            generics,
            params,
            output,
            requires,
            ensures,
            body,
        })
    }
}

/// The names of the functions this crate's expansions extract, unique in the compilation.
fn fresh_name() -> syn::Ident {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    format_ident!(
        "{EXTRACTED_NAME_PREFIX}{}",
        NEXT.fetch_add(1, Ordering::Relaxed)
    )
}

impl BlockContract {
    /// The extracted function, named `name`, with the generics and where clause of the host.
    fn function(
        &self,
        name: &syn::Ident,
        attrs: TokenStream,
        generics: &syn::Generics,
    ) -> TokenStream {
        let BlockContract {
            params, requires, ..
        } = self;
        let (output, ensures, body) = self.in_out_form();
        let params_tokens = params.iter().map(|Param { pat, ty, .. }| quote!(#pat: #ty));
        let (_, _, where_clause) = generics.split_for_impl();
        let generic_params = self.extracted_generics(generics);
        let generics = match generic_params.is_empty() {
            true => quote!(),
            false => quote!(<#(#generic_params),*>),
        };
        quote! {
            #(#[::thrust_macros::requires(#requires)])*
            #(#[::thrust_macros::ensures(#ensures)])*
            #attrs
            #[thrust::extracted_block]
            // a `mut` `&mut` parameter is written through only, which rustc takes for an unused `mut`
            #[allow(unused_mut)]
            fn #name #generics (#(#params_tokens),*) #output #where_clause #body
        }
    }

    /// The generic parameters of the extracted function: the host's, the block's own and one
    /// for each parameter written without a type.
    fn extracted_generics(&self, host: &syn::Generics) -> Vec<TokenStream> {
        let generated = self
            .params
            .iter()
            .filter(|param| param.is_generated)
            .map(|param| &param.ty);
        host.params
            .iter()
            .chain(self.generics.params.iter())
            .map(|param| quote!(#param))
            .chain(generated.map(|ty| quote!(#ty)))
            .collect()
    }

    /// The result type, the `ensures` and the body of the extracted function of a block:
    /// with `mut` parameters it returns `(R, final values)`, the body's value being the first.
    fn in_out_form(&self) -> (TokenStream, Vec<TokenStream>, TokenStream) {
        let BlockContract {
            params,
            output,
            ensures,
            body,
            ..
        } = self;
        let result_ty = match output {
            syn::ReturnType::Default => quote!(()),
            syn::ReturnType::Type(_, ty) => quote!(#ty),
        };
        let in_out: Vec<&Param> = params
            .iter()
            .filter(|param| param.pat.mutability.is_some() && !param.is_mut_ref())
            .collect();
        // A `&mut` parameter not written `mut` is not written through: its final value is its
        // value at the block's start. The spans are the parameter's, which a failure points at.
        let mut ensures = ensures.clone();
        for param in params
            .iter()
            .filter(|param| param.pat.mutability.is_none() && param.is_mut_ref())
        {
            let name = &param.pat.ident;
            ensures.push(quote_spanned!(name.span() => !#name == *#name));
        }
        if in_out.is_empty() {
            return (quote!(-> #result_ty), ensures, quote!(#body));
        }
        let types = in_out.iter().map(|param| &param.ty);
        let names: Vec<&syn::Ident> = in_out.iter().map(|param| &param.pat.ident).collect();
        let output = quote!(-> (#result_ty, #(#types),*));
        let mut projections: Vec<(&syn::Ident, TokenStream)> = Vec::new();
        for (i, name) in names.iter().enumerate() {
            let field = syn::Index::from(i + 1);
            projections.push((name, quote!(result.#field)));
        }
        let result = syn::Ident::new("result", proc_macro2::Span::call_site());
        projections.push((&result, quote!(result.0)));
        let ensures = ensures
            .iter()
            .map(|tokens| rename_in_out(tokens.clone(), &projections))
            .collect();
        let body = quote!({
            let __block_result: #result_ty = #body;
            (__block_result, #(#names),*)
        });
        (output, ensures, body)
    }

    /// The block in place, for `callee`, the function it is extracted into.
    fn at_block(&self, callee: TokenStream) -> TokenStream {
        let arguments = self.params.iter().map(|param| &param.pat.ident);
        let BlockContract { body, output, .. } = self;
        // the body is typed as the written result type, as the extracted function types it
        let result_ty = match output {
            syn::ReturnType::Default => quote!(()),
            syn::ReturnType::Type(_, ty) => quote!(#ty),
        };
        quote! {{
            // one path for the call and the markers, so that the type parameters of the extracted
            // function that the call's arguments fix are the markers' too
            let __block_contract_callee = #callee;
            // the arguments have the outer variables' types, as the call of `callee` would pass
            if false {
                let _ = __block_contract_callee(#(#arguments),*);
                loop {}
            }
            crate::thrust_models::__block_region_open_marker(__block_contract_callee);
            #[allow(unused_variables)]
            let __block_contract_result: #result_ty = #body;
            crate::thrust_models::__block_region_close_marker(__block_contract_callee);
            __block_contract_result
        }}
    }

    /// The function nested at the block and its call, for a block that needs no generics of
    /// its host.
    pub fn expand_nested(&self) -> TokenStream {
        let name = fresh_name();
        let function = self.function(&name, quote!(), &syn::Generics::default());
        let call = self.at_block(quote!(#name));
        quote!({ #function #call })
    }

    /// The number of type and const parameters the block adds to its host's, which the call
    /// leaves to inference.
    fn extra_generic_count(&self) -> usize {
        let own = self
            .generics
            .params
            .iter()
            .filter(|param| !matches!(param, syn::GenericParam::Lifetime(_)));
        own.count()
            + self
                .params
                .iter()
                .filter(|param| param.is_generated)
                .count()
    }

    /// The block in place, for the function `name` hoisted next to its host.
    pub fn hoisted_block(&self, name: &syn::Ident, host: &HoistHost) -> TokenStream {
        let turbofish = host.turbofish(self.extra_generic_count());
        let callee = match host.is_method {
            true => quote!(Self::#name #turbofish),
            false => quote!(#name #turbofish),
        };
        self.at_block(callee)
    }

    /// The function `name` hoisted next to its host, with the host's generics and where clause.
    pub fn hoisted_function(&self, name: &syn::Ident, host: &HoistHost) -> TokenStream {
        let outer_attr = host
            .outer_context
            .map(|outer| quote!(#[thrust::_outer_context(#outer)]));
        let attrs = quote! {
            #outer_attr
            #[::thrust_macros::context]
        };
        self.function(name, attrs, host.generics)
    }
}

/// The prefix of the names of the functions blocks are extracted into.
const EXTRACTED_NAME_PREFIX: &str = "__block_contract_";

/// A new name for a function hoisted next to `host`, unique in the compilation. The name ends in
/// the host's: `__block_contract_<n>_of_<host>`, which Thrust reads to verify the function
/// whenever its host is selected by `THRUST_VERIFY_ONLY` (`selection.rs` reads the same form).
pub fn fresh_hoisted_name(host: &syn::Ident) -> syn::Ident {
    let unique = fresh_name();
    format_ident!("{unique}_of_{host}")
}

/// The enclosing function a block is hoisted from.
pub struct HoistHost<'a> {
    /// The name of the enclosing function.
    pub name: &'a syn::Ident,
    pub generics: &'a syn::Generics,
    /// The enclosing `impl` header, which the hoisted method is stamped with as its host was.
    pub outer_context: Option<&'a crate::FnOuterItem>,
    /// Whether the host is an associated function, so that the hoisted function is one too.
    pub is_method: bool,
}

impl HoistHost<'_> {
    /// `::<T, N, _>`: the host's type and const parameters, which a hoisted function whose
    /// arguments do not mention them cannot infer, and `extra` placeholders for the parameters the
    /// block adds, which its arguments fix. Lifetimes are inferred.
    fn turbofish(&self, extra: usize) -> TokenStream {
        let arguments: Vec<TokenStream> = self
            .generics
            .params
            .iter()
            .filter_map(|param| match param {
                syn::GenericParam::Type(param) => Some(&param.ident),
                syn::GenericParam::Const(param) => Some(&param.ident),
                syn::GenericParam::Lifetime(_) => None,
            })
            .map(|ident| quote!(#ident))
            .chain((0..extra).map(|_| quote!(_)))
            .collect();
        match arguments.is_empty() {
            true => quote!(),
            false => quote!(::<#(#arguments),*>),
        }
    }
}

/// Whether `path` names `block_contract!`.
pub fn is_block_contract(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident == "block_contract")
}

/// `tokens` with each name of `projections` that is not a field or a method (`.x`) replaced by
/// its tokens, and each `old!(x)` by `x`: the names of an `ensures` over the parameters of the
/// function a block is extracted into, read as the entry value, the final value and the
/// result of the function it returns them from.
fn rename_in_out(tokens: TokenStream, projections: &[(&syn::Ident, TokenStream)]) -> TokenStream {
    use proc_macro2::{Delimiter, Group, TokenTree};
    let tokens: Vec<TokenTree> = tokens.into_iter().collect();
    let mut renamed = TokenStream::new();
    let mut i = 0;
    while i < tokens.len() {
        let after_dot =
            i > 0 && matches!(&tokens[i - 1], TokenTree::Punct(p) if p.as_char() == '.');
        if let [TokenTree::Ident(old), TokenTree::Punct(bang), TokenTree::Group(group), ..] =
            &tokens[i..]
        {
            if old == "old" && bang.as_char() == '!' && group.delimiter() == Delimiter::Parenthesis
            {
                renamed.extend(group.stream());
                i += 3;
                continue;
            }
        }
        match &tokens[i] {
            TokenTree::Ident(ident) if !after_dot => {
                match projections.iter().find(|(name, _)| *name == ident) {
                    Some((_, replacement)) => {
                        let group = Group::new(Delimiter::Parenthesis, replacement.clone());
                        renamed.extend([TokenTree::Group(group)]);
                    }
                    None => renamed.extend([TokenTree::Ident(ident.clone())]),
                }
            }
            TokenTree::Group(group) => {
                let mut inner = Group::new(
                    group.delimiter(),
                    rename_in_out(group.stream(), projections),
                );
                inner.set_span(group.span());
                renamed.extend([TokenTree::Group(inner)]);
            }
            token => renamed.extend([token.clone()]),
        }
        i += 1;
    }
    renamed
}

pub fn expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let parsed = match BlockContract::parse_tokens(input.into()) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    parsed.expand_nested().into()
}
