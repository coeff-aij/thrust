//! References from a specification to the ghosts of a labelled `for` loop around it:
//! `iter!('l)`, `iter_old!('l)` and `produced!('l)` name the `iter`, `iter_old` and `produced`
//! of the `for` loop labelled `'l`, as `break 'l` names that loop.
//!
//! [`mod@crate::for_loop`] gives each annotated loop's ghosts names of their own; when the loop
//! has a label, it renames the references to that label in the specifications of its body to
//! those names. A reference is resolved as Rust resolves the label of a `break`: by the innermost
//! enclosing loop or block with that label, within the same function or closure body. A
//! reference that no `for` loop with that ghost resolves is replaced by a compile error. A `for`
//! loop whose body starts with no invariant has its iterator as its only ghost.

use proc_macro2::{Delimiter, Ident, Span, TokenStream, TokenTree};
use syn::visit_mut::VisitMut;

use crate::for_loop::LabelledGhosts;

/// The ghosts of a `for` loop a reference can name.
const GHOSTS: [&str; 3] = ["iter", "iter_old", "produced"];

/// A reference `ghost!('label)`.
pub struct Reference {
    pub ghost: String,
    pub label: String,
    pub span: Span,
}

impl Reference {
    fn display(&self) -> String {
        format!("{}!({})", self.ghost, self.label)
    }
}

/// The reference whose macro is named `name` and takes `args`, a parenthesized label.
fn reference_of(name: &Ident, parenthesized: bool, args: TokenStream) -> Option<Reference> {
    if !parenthesized {
        return None;
    }
    let ghost = GHOSTS.iter().find(|ghost| name == *ghost)?;
    let label: syn::Lifetime = syn::parse2(args).ok()?;
    Some(Reference {
        ghost: ghost.to_string(),
        label: label.to_string(),
        span: name.span(),
    })
}

/// The reference `tokens` starts with: a ghost's name, `!`, and a parenthesized label.
pub fn reference_at(tokens: &[TokenTree]) -> Option<Reference> {
    let [TokenTree::Ident(name), TokenTree::Punct(bang), TokenTree::Group(group), ..] = tokens
    else {
        return None;
    };
    if bang.as_char() != '!' {
        return None;
    }
    reference_of(
        name,
        group.delimiter() == Delimiter::Parenthesis,
        group.stream(),
    )
}

/// The reference `mac` is, written in a pattern.
fn reference_of_macro(mac: &syn::Macro) -> Option<Reference> {
    let parenthesized = matches!(mac.delimiter, syn::MacroDelimiter::Paren(_));
    reference_of(mac.path.get_ident()?, parenthesized, mac.tokens.clone())
}

/// The references in `tokens`, at any depth.
pub fn references(tokens: &TokenStream) -> Vec<Reference> {
    let tokens: Vec<TokenTree> = tokens.clone().into_iter().collect();
    let mut found = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        if let Some(reference) = reference_at(&tokens[i..]) {
            found.push(reference);
        } else if let TokenTree::Group(group) = token {
            found.extend(references(&group.stream()));
        }
    }
    found
}

/// `tokens` with each reference to `label` replaced by the name `renames` gives its ghost,
/// spanned as the reference's ghost name.
fn rename(tokens: TokenStream, label: &str, renames: &[(&str, &Ident)]) -> TokenStream {
    let tokens: Vec<TokenTree> = tokens.into_iter().collect();
    let mut renamed = Vec::with_capacity(tokens.len());
    let mut i = 0;
    while i < tokens.len() {
        let target = reference_at(&tokens[i..])
            .filter(|reference| reference.label == label)
            .and_then(|reference| {
                let (_, to) = renames.iter().find(|(from, _)| *from == reference.ghost)?;
                Some(Ident::new(&to.to_string(), reference.span))
            });
        if let Some(target) = target {
            renamed.push(TokenTree::Ident(target));
            i += 3;
            continue;
        }
        renamed.push(match &tokens[i] {
            TokenTree::Group(group) => {
                let mut inner = proc_macro2::Group::new(
                    group.delimiter(),
                    rename(group.stream(), label, renames),
                );
                inner.set_span(group.span());
                TokenTree::Group(inner)
            }
            token => token.clone(),
        });
        i += 1;
    }
    renamed.into_iter().collect()
}

/// Whether `path` names a specification macro whose formula names live variables, where a
/// reference may appear. `closure!` is not one: a label does not reach into a closure.
pub fn is_formula_macro(path: &syn::Path) -> bool {
    let Some(segment) = path.segments.last() else {
        return false;
    };
    let name = segment.ident.to_string();
    crate::invariant::Marker::of_macro(&name).is_some()
        || crate::invariant::Marker::statement_of_macro(&name).is_some()
        || name == "ghost"
}

/// The closure parameters of a formula macro's `tokens`, between the first two `|`, and the
/// tokens after them; `None` when there is no such header.
fn split_params(tokens: &TokenStream) -> Option<(TokenStream, TokenStream)> {
    let tokens: Vec<TokenTree> = tokens.clone().into_iter().collect();
    let mut bars = tokens
        .iter()
        .enumerate()
        .filter(|(_, token)| matches!(token, TokenTree::Punct(p) if p.as_char() == '|'))
        .map(|(i, _)| i);
    let open = bars.next()?;
    let close = bars.next()?;
    let params = tokens[open + 1..close].iter().cloned().collect();
    let rest = tokens[close + 1..].iter().cloned().collect();
    Some((params, rest))
}

/// The parameter `pat_type` as the plain name of the ghost it names and its written type, when
/// it is a reference to `label`.
pub fn typed_reference(pat_type: &syn::PatType, label: &str) -> Option<(Ident, syn::Type)> {
    let syn::Pat::Macro(pat_macro) = &*pat_type.pat else {
        return None;
    };
    let reference = reference_of_macro(&pat_macro.mac)?;
    (reference.label == label).then(|| {
        (
            Ident::new(&reference.ghost, reference.span),
            (*pat_type.ty).clone(),
        )
    })
}

/// The parameters of `mac`, a formula macro, that are references to `label` (see
/// [`typed_reference`]).
fn typed_references(mac: &syn::Macro, label: &str) -> Vec<(Ident, syn::Type)> {
    let wrapped = crate::formula::wrap_closure_body(mac.tokens.clone());
    let Ok(closure) = syn::parse2::<syn::ExprClosure>(wrapped) else {
        return Vec::new();
    };
    closure
        .inputs
        .iter()
        .filter_map(|input| match input {
            syn::Pat::Type(pat_type) => typed_reference(pat_type, label),
            _ => None,
        })
        .collect()
}

/// The reference to `label` that the formula of `mac` uses but its parameters do not declare.
fn undeclared_reference(mac: &syn::Macro, label: &str) -> Option<Reference> {
    let (params, formula) = split_params(&mac.tokens)?;
    let declared: Vec<String> = references(&params)
        .into_iter()
        .filter(|reference| reference.label == label)
        .map(|reference| reference.ghost)
        .collect();
    references(&formula)
        .into_iter()
        .find(|reference| reference.label == label && !declared.contains(&reference.ghost))
}

/// Replaces `mac` with a `compile_error!` of `message` at `span`.
pub fn replace_with_error(mac: &mut syn::Macro, span: Span, message: &str) {
    mac.path = syn::parse_quote_spanned!(span=> ::core::compile_error);
    mac.delimiter = syn::MacroDelimiter::Paren(syn::token::Paren(span));
    mac.tokens = quote::quote_spanned!(span=> #message);
}

/// Renames the references to `label` in `mac`, a formula macro, to the names `renames` gives,
/// and returns its parameters that are such references, typed. A formula naming a reference
/// its parameters do not declare becomes a compile error.
pub fn rename_macro(
    mac: &mut syn::Macro,
    label: &str,
    renames: &[(&str, &Ident)],
) -> Vec<(Ident, syn::Type)> {
    if let Some(reference) = undeclared_reference(mac, label) {
        let message = format!(
            "`{0}` is used in the formula but is not one of its parameters: add `{0}: <type>`",
            reference.display()
        );
        replace_with_error(mac, reference.span, &message);
        return Vec::new();
    }
    let typed = typed_references(mac, label);
    mac.tokens = rename(mac.tokens.clone(), label, renames);
    typed
}

/// The label of `expr` when it is a loop or a block, which a reference can resolve to.
fn label_of(expr: &syn::Expr) -> Option<&syn::Label> {
    match expr {
        syn::Expr::ForLoop(e) => e.label.as_ref(),
        syn::Expr::While(e) => e.label.as_ref(),
        syn::Expr::Loop(e) => e.label.as_ref(),
        syn::Expr::Block(e) => e.label.as_ref(),
        _ => None,
    }
}

/// Visits the formula macros of a body that a reference to `label` written there resolves to
/// the body's loop: not those inside a closure, an `async` block or a nested item, nor those
/// inside a nested loop or block with the same label, which shadows it.
struct LabelReach<'a, F> {
    label: &'a str,
    on_macro: F,
}

impl<F: FnMut(&mut syn::Macro)> VisitMut for LabelReach<'_, F> {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        if matches!(expr, syn::Expr::Closure(_) | syn::Expr::Async(_)) {
            return;
        }
        if label_of(expr).is_some_and(|label| label.name.to_string() == self.label) {
            return;
        }
        syn::visit_mut::visit_expr_mut(self, expr);
    }

    fn visit_item_mut(&mut self, _: &mut syn::Item) {}

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if is_formula_macro(&mac.path) {
            (self.on_macro)(mac);
        }
    }
}

/// Renames the references to `label` in the formula macros of `stmts`, the body of the loop
/// labelled `label`, and returns the typed parameters they declare (see [`rename_macro`]).
pub fn rename_in_body(
    stmts: &mut [syn::Stmt],
    label: &str,
    renames: &[(&str, &Ident)],
) -> Vec<(Ident, syn::Type)> {
    let mut typed = Vec::new();
    let mut reach = LabelReach {
        label,
        on_macro: |mac: &mut syn::Macro| typed.extend(rename_macro(mac, label, renames)),
    };
    for stmt in stmts {
        reach.visit_stmt_mut(stmt);
    }
    typed
}

/// Whether a formula macro of `stmts`, the body of the loop labelled `label`, references `label`.
pub fn is_referenced_in_body(stmts: &[syn::Stmt], label: &str) -> bool {
    let mut stmts = stmts.to_vec();
    let mut referenced = false;
    let mut reach = LabelReach {
        label,
        on_macro: |mac: &mut syn::Macro| {
            referenced |= references(&mac.tokens)
                .iter()
                .any(|reference| reference.label == label);
        },
    };
    for stmt in &mut stmts {
        reach.visit_stmt_mut(stmt);
    }
    referenced
}

/// Replaces the references to the label of `expr` in its body by compile errors, when they name
/// a ghost the labelled loop or block does not have: any ghost of a `while` or `loop` or a block,
/// and of a `for` loop those `labelled_ghosts` does not give.
pub fn reject_in_labelled(
    expr: &mut syn::Expr,
    labelled_ghosts: impl Fn(&syn::ExprForLoop) -> LabelledGhosts,
) {
    let Some(label) = label_of(expr).map(|label| label.name.to_string()) else {
        return;
    };
    let (what, named): (&str, &[&str]) = match &*expr {
        syn::Expr::ForLoop(for_loop) => match labelled_ghosts(for_loop) {
            LabelledGhosts::All => return,
            LabelledGhosts::Iter => ("a `for` loop with no invariant, which keeps no history: only its iterator has a ghost", &["iter"]),
            LabelledGhosts::None => ("a `for` loop whose leading invariants do not name `iter`, so its iterator has no ghost", &[]),
        },
        syn::Expr::While(_) => ("a `while` loop", &[]),
        syn::Expr::Loop(_) => ("a `loop`", &[]),
        _ => ("a block", &[]),
    };
    let mut reach = LabelReach {
        label: &label,
        on_macro: |mac: &mut syn::Macro| {
            let reference = references(&mac.tokens).into_iter().find(|reference| {
                reference.label == label && !named.contains(&reference.ghost.as_str())
            });
            if let Some(reference) = reference {
                let message = format!(
                    "`{}` names a ghost of a `for` loop, but `{}` labels {what}",
                    reference.display(),
                    label
                );
                replace_with_error(mac, reference.span, &message);
            }
        },
    };
    syn::visit_mut::visit_expr_mut(&mut reach, expr);
}

/// The error for a reference no enclosing loop resolves, from within `#[thrust_macros::context]`.
pub fn unresolved_message(reference: &Reference) -> String {
    format!(
        "no loop labelled `{}` encloses `{}` in this function or closure body",
        reference.label,
        reference.display()
    )
}

/// The error for a reference in a specification outside `#[thrust_macros::context]`, or `None`
/// when `tokens` has no reference.
pub fn outside_context_error(tokens: &TokenStream) -> Option<syn::Error> {
    let reference = references(tokens).into_iter().next()?;
    Some(syn::Error::new(
        reference.span,
        format!(
            "`{}` is resolved by `#[thrust_macros::context]` on the enclosing function",
            reference.display()
        ),
    ))
}
