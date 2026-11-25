//! Expansion of `thrust_macros::block_contract_fn!`, a contract on a block written as the
//! function the block would be extracted into:
//!
//! ```ignore
//! block_contract_fn!(
//!     |a1: T1, a2: &mut T2, a3: &T3| -> R
//!     requires(REQUIRES),
//!     ensures(ENSURES),
//!     { BODY }
//! )
//! ```
//!
//! The form is a function with exactly that signature and contract, and a call of it at the
//! block's place that passes the outer variable of each parameter's name: `&a3` for a parameter
//! written `&T`, `&mut a2` for one written `&mut T`, and `a1` otherwise. Where the outer variable
//! is itself a reference, deref coercion turns `&&T` into `&T` and `&mut &mut T` into `&mut T`,
//! the latter only when the outer binding is declared `mut`. The body can name only its
//! parameters (rustc reports E0434 for anything else), which is what makes the contract complete.
//! The block is the same as an extracted function: a `return` or `?` in the body leaves the
//! block with the written result type, and a `break` or `continue` aimed at a loop outside is a
//! rustc error. To exit an outer loop or function, write the result type as `Result` or
//! `ControlFlow` and handle it at the call (`block_contract_fn!(..)?`, or a `match`).
//!
//! `block_contract_inline!` takes the same notation and runs the body in place, where
//! `block_contract_fn!` replaces it by the call. The block is verified as if it were extracted
//! into the function of that signature and contract, which is generated from the same text (see
//! [`Mode::Inline`]).
//!
//! Without `#[thrust_macros::context]` the function is nested at the block, which cannot use the
//! enclosing function's generics. Under it the function is hoisted next to the enclosing
//! function, with that function's generic parameters and where clause, and called by path (see
//! [`Hoisted`]).

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::parse::{Parse, ParseStream};

mod kw {
    syn::custom_keyword!(requires);
    syn::custom_keyword!(ensures);
}

/// What the block does where it is written.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// `block_contract_fn!`: the block is replaced by a call of the extracted function.
    Call,
    /// `block_contract_inline!`: the body runs in place between two markers that name the
    /// extracted function, and the analysis reads the region as a call of it. The function takes
    /// the outer variables with their own types, the type check of a call that never runs
    /// ensures that. A parameter written `mut` may be changed by the body, and the function
    /// returns its final value after the result, so that `ensures` names the final value as `x`,
    /// the entry value as `old!(x)` and the result as `result`, as in a function with `&mut`.
    Inline,
}

/// The parsed form: the parameters, the result type, the contract and the block.
pub struct BlockContractFn {
    mode: Mode,
    params: Vec<Param>,
    output: syn::ReturnType,
    requires: Vec<TokenStream>,
    ensures: Vec<TokenStream>,
    body: syn::Block,
}

/// A parameter: `mut? name: ty`.
struct Param {
    pat: syn::PatIdent,
    ty: syn::Type,
}

impl Param {
    /// The argument that passes the outer variable of this parameter's name.
    fn argument(&self) -> TokenStream {
        let name = &self.pat.ident;
        match &self.ty {
            syn::Type::Reference(reference) if reference.mutability.is_some() => quote!(&mut #name),
            syn::Type::Reference(_) => quote!(&#name),
            _ => quote!(#name),
        }
    }
}

impl Parse for Param {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let pat_type: syn::PatType = input.parse()?;
        let syn::Pat::Ident(pat) = *pat_type.pat else {
            return Err(syn::Error::new_spanned(
                pat_type.pat,
                "a parameter is a name: it takes the outer variable of that name",
            ));
        };
        if pat.by_ref.is_some() || pat.subpat.is_some() {
            return Err(syn::Error::new_spanned(
                pat,
                "a parameter is a name: it takes the outer variable of that name",
            ));
        }
        Ok(Param {
            pat,
            ty: *pat_type.ty,
        })
    }
}

fn clause<K: Parse>(input: ParseStream) -> syn::Result<TokenStream> {
    input.parse::<K>()?;
    let content;
    syn::parenthesized!(content in input);
    content.parse()
}

impl BlockContractFn {
    /// The form written as `tokens`, of the macro of `mode`.
    pub fn parse_for(tokens: TokenStream, mode: Mode) -> syn::Result<Self> {
        syn::parse::Parser::parse2(|input: ParseStream| Self::parse_in(input, mode), tokens)
    }

    fn parse_in(input: ParseStream, mode: Mode) -> syn::Result<Self> {
        input.parse::<syn::Token![|]>()?;
        let mut params = Vec::new();
        while !input.peek(syn::Token![|]) {
            params.push(input.parse()?);
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
        Ok(BlockContractFn {
            mode,
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
    format_ident!("__block_contract_{}", NEXT.fetch_add(1, Ordering::Relaxed))
}

impl BlockContractFn {
    /// The call of the extracted function `callee`, passing the outer variables.
    fn call(&self, callee: TokenStream) -> TokenStream {
        let arguments = self.params.iter().map(Param::argument);
        quote!(#callee(#(#arguments),*))
    }

    /// The extracted function, named `name`, with the generics and where clause of the host.
    fn function(
        &self,
        name: &syn::Ident,
        attrs: TokenStream,
        generics: &syn::Generics,
    ) -> TokenStream {
        let BlockContractFn {
            mode,
            params,
            output,
            requires,
            ensures,
            body,
        } = self;
        let (output, ensures, body) = match mode {
            Mode::Call => (quote!(#output), ensures.clone(), quote!(#body)),
            Mode::Inline => self.in_out_form(),
        };
        let params = params.iter().map(|Param { pat, ty }| quote!(#pat: #ty));
        let (_, _, where_clause) = generics.split_for_impl();
        let generic_params = &generics.params;
        let generics = match generic_params.is_empty() {
            true => quote!(),
            false => quote!(<#generic_params>),
        };
        quote! {
            #(#[::thrust_macros::requires(#requires)])*
            #(#[::thrust_macros::ensures(#ensures)])*
            #attrs
            fn #name #generics (#(#params),*) #output #where_clause #body
        }
    }

    /// The result type, the `ensures` and the body of the extracted function of an inline block:
    /// with `mut` parameters it returns `(R, final values)`, the body's value being the first.
    fn in_out_form(&self) -> (TokenStream, Vec<TokenStream>, TokenStream) {
        let BlockContractFn {
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
            .filter(|param| param.pat.mutability.is_some())
            .collect();
        if in_out.is_empty() {
            return (quote!(-> #result_ty), ensures.clone(), quote!(#body));
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

    /// Whether the body runs where the block is written.
    pub fn runs_in_place(&self) -> bool {
        self.mode == Mode::Inline
    }

    /// The block in place, for `callee`, the function it is extracted into.
    fn in_place(&self, callee: TokenStream) -> TokenStream {
        let arguments = self.params.iter().map(|param| &param.pat.ident);
        let BlockContractFn { body, .. } = self;
        quote! {{
            // the arguments have the outer variables' types, as the call of `callee` would pass
            if false {
                let _ = #callee(#(#arguments),*);
                loop {}
            }
            crate::thrust_models::__block_region_open_marker(#callee);
            #[allow(unused_variables)]
            let __block_contract_result = #body;
            crate::thrust_models::__block_region_close_marker(#callee);
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

    /// The call of the function `name` hoisted next to its host, which replaces the block.
    pub fn hoisted_call(&self, name: &syn::Ident, host: &HoistHost) -> TokenStream {
        let turbofish = host.turbofish();
        let callee = match host.is_method {
            true => quote!(Self::#name #turbofish),
            false => quote!(#name #turbofish),
        };
        self.at_block(callee)
    }

    /// What replaces the block: the call of `callee`, or the body in place for an inline block.
    fn at_block(&self, callee: TokenStream) -> TokenStream {
        match self.mode {
            Mode::Call => self.call(callee),
            Mode::Inline => self.in_place(callee),
        }
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

/// A new name for a hoisted function, unique in the compilation.
pub fn fresh_hoisted_name() -> syn::Ident {
    fresh_name()
}

/// The enclosing function a block is hoisted from.
pub struct HoistHost<'a> {
    pub generics: &'a syn::Generics,
    /// The enclosing `impl` header, which the hoisted method is stamped with as its host was.
    pub outer_context: Option<&'a crate::FnOuterItem>,
    /// Whether the host is an associated function, so that the hoisted function is one too.
    pub is_method: bool,
}

impl HoistHost<'_> {
    /// `::<T, N>`: the type and const parameters, which a hoisted function whose arguments do not
    /// mention them cannot infer. Lifetimes are inferred.
    fn turbofish(&self) -> TokenStream {
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
            .collect();
        match arguments.is_empty() {
            true => quote!(),
            false => quote!(::<#(#arguments),*>),
        }
    }
}

/// The mode of the macro `path` names, if it is `block_contract_fn!` or `block_contract_inline!`.
pub fn mode_of(path: &syn::Path) -> Option<Mode> {
    let name = &path.segments.last()?.ident;
    if name == "block_contract_fn" {
        Some(Mode::Call)
    } else if name == "block_contract_inline" {
        Some(Mode::Inline)
    } else {
        None
    }
}

/// `tokens` with each name of `projections` that is not a field or a method (`.x`) replaced by
/// its tokens, and each `old!(x)` by `x`: the names of an `ensures` over the parameters of the
/// function an inline block is extracted into, read as the entry value, the final value and the
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
    expand_in(input, Mode::Call)
}

pub fn expand_inline(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    expand_in(input, Mode::Inline)
}

fn expand_in(input: proc_macro::TokenStream, mode: Mode) -> proc_macro::TokenStream {
    let parsed = match BlockContractFn::parse_for(input.into(), mode) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    parsed.expand_nested().into()
}
