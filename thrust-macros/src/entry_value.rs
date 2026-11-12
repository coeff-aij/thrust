//! `old!(x)` in a loop invariant: the value the parameter `x` of the enclosing function had on
//! entry, as `old(x)` in Prusti, and in Verus for `&mut` parameters. The invariant declares it as a parameter
//! `old!(x): T`, with the type of the function's parameter, and its formula reads it as
//! `old!(x)`; it may name `x` as well, the variable's value at the loop head.
//!
//! Both are renamed to the parameter `__thrust_old_x` of the lifted formula function (with
//! `old!(self)` spelled `__thrust_old_self`), which the analyzer binds to the entry value of the
//! parameter `x`. The renaming works on tokens, before the formula's body is wrapped in the macro
//! that translates it, so that it reaches every `old!(x)` at any depth.

use proc_macro2::{Delimiter, Group, Ident, TokenStream, TokenTree};

/// The prefix of the lifted formula function's parameter that names a parameter's entry value.
pub const PARAM_PREFIX: &str = "__thrust_old_";

/// `tokens`, a loop invariant's closure (after the host's signature under a context), with every
/// `old!(x)` renamed to `__thrust_old_x`; an error at an `old!` whose argument is not a single
/// name, or that the formula reads without a parameter `old!(x): T` declaring it.
pub fn rename_in_invariant(tokens: TokenStream) -> syn::Result<TokenStream> {
    check_declared(&tokens)?;
    rename(tokens)
}

/// An error at the first `old!` in `tokens`, the closure of a statement form, which has no entry
/// values to name.
pub fn reject(tokens: &TokenStream) -> syn::Result<()> {
    match references(tokens)?.first() {
        Some(param) => Err(syn::Error::new(
            param.span(),
            "`old!` names a parameter's entry value only in `invariant!` and `partial_invariant!`",
        )),
        None => Ok(()),
    }
}

/// An error at the first `old!(x)` the body of the closure reads that its parameters do not
/// declare. The parameters are the tokens between the first two `|`, as
/// [`crate::formula::wrap_closure_body`] takes them.
fn check_declared(tokens: &TokenStream) -> syn::Result<()> {
    let tokens: Vec<TokenTree> = tokens.clone().into_iter().collect();
    let bars: Vec<usize> = tokens
        .iter()
        .enumerate()
        .filter(|(_, token)| matches!(token, TokenTree::Punct(p) if p.as_char() == '|'))
        .map(|(i, _)| i)
        .take(2)
        .collect();
    let [open, close] = bars[..] else {
        return Ok(());
    };
    let declared = references(&tokens[open + 1..close].iter().cloned().collect())?;
    let read = references(&tokens[close + 1..].iter().cloned().collect())?;
    match read.iter().find(|param| !declared.contains(param)) {
        Some(param) => Err(syn::Error::new(
            param.span(),
            format!(
                "the invariant reads `old!({param})` but does not declare it: add a parameter \
                 `old!({param}): T` with the type of the function's parameter `{param}`"
            ),
        )),
        None => Ok(()),
    }
}

/// The parameters named by the `old!(x)` in `tokens`, at any depth.
fn references(tokens: &TokenStream) -> syn::Result<Vec<Ident>> {
    let tokens: Vec<TokenTree> = tokens.clone().into_iter().collect();
    let mut found = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        if let Some(param) = reference_at(&tokens[i..])? {
            found.push(param);
        } else if let TokenTree::Group(group) = token {
            found.extend(references(&group.stream())?);
        }
    }
    Ok(found)
}

/// `tokens` with every `old!(x)` renamed to `__thrust_old_x`.
fn rename(tokens: TokenStream) -> syn::Result<TokenStream> {
    let tokens: Vec<TokenTree> = tokens.into_iter().collect();
    let mut renamed = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        if let Some(param) = reference_at(&tokens[i..])? {
            renamed.push(TokenTree::Ident(Ident::new(
                &format!("{PARAM_PREFIX}{param}"),
                param.span(),
            )));
            i += 3;
            continue;
        }
        renamed.push(match &tokens[i] {
            TokenTree::Group(group) => {
                let mut inner = Group::new(group.delimiter(), rename(group.stream())?);
                inner.set_span(group.span());
                TokenTree::Group(inner)
            }
            token => token.clone(),
        });
        i += 1;
    }
    Ok(renamed.into_iter().collect())
}

/// The parameter named by the `old!(x)` `tokens` start with.
fn reference_at(tokens: &[TokenTree]) -> syn::Result<Option<Ident>> {
    let [TokenTree::Ident(name), TokenTree::Punct(bang), TokenTree::Group(group), ..] = tokens
    else {
        return Ok(None);
    };
    if name != "old" || bang.as_char() != '!' || group.delimiter() != Delimiter::Parenthesis {
        return Ok(None);
    }
    let args: Vec<TokenTree> = group.stream().into_iter().collect();
    match &args[..] {
        [TokenTree::Ident(param)] => Ok(Some(param.clone())),
        _ => Err(syn::Error::new(
            name.span(),
            "`old!` takes the name of a parameter of the function, as in `old!(x)`",
        )),
    }
}
