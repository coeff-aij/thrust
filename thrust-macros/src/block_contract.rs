//! Expansion of `thrust_macros::block_contract!(requires(..), ensures(..), { .. })`, a contract
//! on a braced block, as ACSL's statement contracts and Why3's abstract blocks
//! (`begin ensures { .. } e end`) are: the block is checked once from `requires` against
//! `ensures`, and the code after it reads only the contract. The braces make the code
//! single-entry by its syntax.
//!
//! The form expands into the block between the two marker forms the analysis reads:
//!
//! ```ignore
//! {
//!     ::thrust_macros::block_requires!(REQUIRES);
//!     let result = { BODY };
//!     ::thrust_macros::block_ensures!(ENSURES);
//!     result
//! }
//! ```
//!
//! so that `ensures` names the block's value as `result`, as a function's `ensures` does. Under
//! `#[thrust_macros::context]` the injector rewrites the form into
//! `_block_contract_with_context!`, whose two formulas carry the host function's context and
//! expand into the context-carrying markers.

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream};

/// The parsed arguments: the two formulas, as the tokens of their closures, and the block.
pub struct BlockContract {
    pub requires: TokenStream,
    pub ensures: TokenStream,
    pub body: syn::Block,
}

/// `name(TOKENS)`, the tokens of one of the two clauses.
fn clause(input: ParseStream, name: &str) -> syn::Result<TokenStream> {
    let ident: syn::Ident = input.parse()?;
    if ident != name {
        return Err(syn::Error::new(
            ident.span(),
            format!("expected `{name}(..)`"),
        ));
    }
    let content;
    syn::parenthesized!(content in input);
    content.parse()
}

impl Parse for BlockContract {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let requires = clause(input, "requires")?;
        input.parse::<syn::Token![,]>()?;
        let ensures = clause(input, "ensures")?;
        input.parse::<syn::Token![,]>()?;
        let body = input.parse()?;
        input.parse::<Option<syn::Token![,]>>()?;
        Ok(BlockContract {
            requires,
            ensures,
            body,
        })
    }
}

impl BlockContract {
    /// The tokens of the arguments, as `parse` reads them.
    pub fn to_arguments(&self) -> TokenStream {
        let BlockContract {
            requires,
            ensures,
            body,
        } = self;
        quote!(requires(#requires), ensures(#ensures), #body)
    }
}

/// Expands the form, with the markers carrying the host function's context when
/// `with_context` (the injector put the context into both formulas).
pub fn expand(input: proc_macro::TokenStream, with_context: bool) -> proc_macro::TokenStream {
    let BlockContract {
        requires,
        ensures,
        body,
    } = match syn::parse::<BlockContract>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    let (open, close) = match with_context {
        true => (
            quote!(::thrust_macros::_block_requires_with_context),
            quote!(::thrust_macros::_block_ensures_with_context),
        ),
        false => (
            quote!(::thrust_macros::block_requires),
            quote!(::thrust_macros::block_ensures),
        ),
    };
    // `result` at the call site, so that the `ensures` closure's `result` names it
    let result = syn::Ident::new("result", Span::call_site());
    quote! {
        {
            #open!(#requires);
            #[allow(unused_variables)]
            let #result = #body;
            #close!(#ensures);
            #result
        }
    }
    .into()
}
