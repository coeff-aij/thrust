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

/// The parsed form: the parameters, the result type, the contract and the block.
pub struct BlockContractFn {
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

impl Parse for BlockContractFn {
    fn parse(input: ParseStream) -> syn::Result<Self> {
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
            params,
            output,
            requires,
            ensures,
            body,
        } = self;
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

    /// The function nested at the block and its call, for a block that needs no generics of
    /// its host.
    pub fn expand_nested(&self) -> TokenStream {
        let name = fresh_name();
        let function = self.function(&name, quote!(), &syn::Generics::default());
        let call = self.call(quote!(#name));
        quote!({ #function #call })
    }

    /// The function hoisted next to its host and the call of it that replaces the block.
    pub fn hoist(&self, host: &HoistHost) -> Hoisted {
        let name = fresh_name();
        let outer_attr = host
            .outer_context
            .as_ref()
            .map(|outer| quote!(#[thrust::_outer_context(#outer)]));
        let attrs = quote! {
            #outer_attr
            #[::thrust_macros::context]
        };
        let function = self.function(&name, attrs, host.generics);
        let turbofish = host.turbofish();
        let callee = match host.is_method {
            true => quote!(Self::#name #turbofish),
            false => quote!(#name #turbofish),
        };
        Hoisted {
            function,
            call: self.call(callee),
        }
    }
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

/// A hoisted block: the item to emit beside the host and the expression to put at the block.
pub struct Hoisted {
    pub function: TokenStream,
    pub call: TokenStream,
}

/// Whether `path` names `block_contract_fn!`.
pub fn is_block_contract_fn(path: &syn::Path) -> bool {
    path.segments
        .last()
        .is_some_and(|segment| segment.ident == "block_contract_fn")
}

pub fn expand(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let parsed = match syn::parse::<BlockContractFn>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    parsed.expand_nested().into()
}
