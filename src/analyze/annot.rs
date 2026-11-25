//! Supporting implementation for parsing Thrust annotations.

use rustc_ast::tokenstream::TokenStream;
use rustc_hir::def_id::DefId;
use rustc_hir::Attribute;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Symbol;

use crate::rty;

/// Defines one function per path of a Thrust item or attribute, each returning the path's
/// segments: `attr` paths are `thrust::<name>` (attributes), `def` paths are
/// `thrust::def::<name>` (items of the model, sequence, logic and marker library in std.rs).
macro_rules! thrust_paths {
    ($kind:ident; $($(#[$doc:meta])* $fn_name:ident = $segment:literal;)*) => {
        $(
            $(#[$doc])*
            pub fn $fn_name() -> thrust_paths!(@ty $kind) {
                thrust_paths!(@path $kind, $segment)
            }
        )*
    };
    (@ty attr) => { [Symbol; 2] };
    (@ty def) => { [Symbol; 3] };
    (@path attr, $segment:literal) => { [Symbol::intern("thrust"), Symbol::intern($segment)] };
    (@path def, $segment:literal) => {
        [Symbol::intern("thrust"), Symbol::intern("def"), Symbol::intern($segment)]
    };
}

thrust_paths! {
    attr;
    trusted_path = "trusted";
    sealed_path = "sealed";
    opaque_path = "opaque";
    split_goals_path = "split_goals";
    reveal_path = "reveal";
    callable_path = "callable";
    extern_spec_fn_path = "extern_spec_fn";
    raw_command_path = "raw_command";
    predicate_path = "predicate";
    logic_path = "logic";
    lemma_path = "lemma";
    lemma_rec_path = "lemma_rec";
    derived_path = "derived";
    law_path = "law";
    ignored_path = "ignored";
    formula_fn_path = "formula_fn";
    variant_path_path = "variant_path";
    requires_path_path = "requires_path";
    ensures_path_path = "ensures_path";
    refinement_path_path = "refinement_path";
    hist_inv_path_path = "hist_inv_path";
    /// `#[thrust::open_inv]` on a parameter: its type invariant is neither assumed at entry nor, for a
    /// `&mut`, required of its final value (Creusot's `#[creusot::open_inv]`).
    open_inv_path = "open_inv";
    /// `#[thrust::open_inv_result]` on a function: its result's type invariant is not ensured
    /// (Creusot's `#[open_inv_result]`).
    open_inv_result_path = "open_inv_result";
    closure_upvars_path = "closure_upvars";
}

thrust_paths! {
    def;
    type_invariant_path = "type_invariant";
    model_ty_path = "model_ty";
    int_model_path = "int_model";
    uint_model_path = "uint_model";
    int_n_model_path = "int_n_model";
    uint_n_model_path = "uint_n_model";
    bit_vec_model_path = "bit_vec_model";
    bit_vec_from_int_path = "bit_vec_from_int";
    bit_vec_to_int_path = "bit_vec_to_int";
    mut_model_path = "mut_model";
    box_model_path = "box_model";
    array_model_path = "array_model";
    closure_model_path = "closure_model";
    iterator_spec_path = "iterator_spec";
    partial_ord_spec_path = "partial_ord_spec";
    model_eq_path = "model_eq";
    no_model_path = "no_model";
    dyn_model_path = "dyn_model";
    ghost_model_path = "ghost_model";
    mut_model_new_path = "mut_new";
    box_model_new_path = "box_new";
    array_model_store_path = "array_store";
    array_model_from_fn_path = "array_from_fn";
    seq_model_path = "seq_model";
    seq_empty_path = "seq_empty";
    int_to_int_n_path = "int_to_int_n";
    proof_branch_path = "proof_branch";
    int_lit_path = "int_lit";
    int_n_to_int_path = "int_n_to_int";
    uint_to_uint_n_path = "uint_to_uint_n";
    uint_n_to_uint_path = "uint_n_to_uint";
    seq_singleton_path = "seq_singleton";
    seq_len_path = "seq_len";
    seq_push_path = "seq_push";
    seq_store_path = "seq_store";
    seq_subsequence_path = "seq_subsequence";
    seq_concat_path = "seq_concat";
    exists_path = "exists";
    forall_path = "forall";
    implies_path = "implies";
    log_eq_args_path = "log_eq_args";
    invariant_marker_path = "invariant_marker";
    partial_invariant_marker_path = "partial_invariant_marker";
    for_loop_history_marker_path = "for_loop_history_marker";
    for_loop_history_path = "for_loop_history";
    for_loop_iter_old_marker_path = "for_loop_iter_old_marker";
    for_loop_iter_old_path = "for_loop_iter_old";
    for_loop_produced_marker_path = "for_loop_produced_marker";
    for_loop_produced_path = "for_loop_produced";
    for_loop_produced_push_marker_path = "for_loop_produced_push_marker";
    for_loop_produced_push_path = "for_loop_produced_push";
    assert_marker_path = "assert_marker";
    assume_marker_path = "assume_marker";
    block_region_open_marker_path = "block_region_open_marker";
    block_region_close_marker_path = "block_region_close_marker";
    choose_marker_path = "choose_marker";
    witness_path = "witness";
    ghost_marker_path = "ghost_marker";
    fn_param_wrapper_path = "fn_param_wrapper";
    fn_param_at_entry_path = "fn_param_at_entry";
    closure_precondition_path = "closure_precondition";
    closure_postcondition_path = "closure_postcondition";
    closure_hist_inv_path = "closure_hist_inv";
}

pub fn extract_annot_tokens(attr: Attribute) -> TokenStream {
    let Attribute::Unparsed(item) = attr else {
        panic!("invalid attribute: expected unparsed");
    };
    let rustc_hir::AttrArgs::Delimited(d) = item.args else {
        panic!("invalid attribute: expected delimited args");
    };
    d.tokens
}

/// Parses a [`rty::TypePosition`] from the tokens of a
/// `#[thrust::refinement_path(..)]` attribute.
///
/// Tokens are comma-separated [`rty::TypePositionStep`]s, each encoded as
/// `result` (→ `Return`), `$i` (→ `Param(i)`), or a bare integer `i` (→
/// `TypeArg(i)`).
pub fn parse_type_position(ts: &TokenStream) -> rty::TypePosition {
    use rustc_ast::token::{LitKind, TokenKind};
    use rustc_ast::tokenstream::TokenTree;

    let parse_int = |lit: &rustc_ast::token::Lit| -> usize {
        assert_eq!(
            lit.kind,
            LitKind::Integer,
            "expected an integer in type position"
        );
        lit.symbol
            .as_str()
            .parse()
            .expect("invalid integer in type position")
    };

    let mut steps = Vec::new();
    let mut iter = ts.iter();
    while let Some(tt) = iter.next() {
        let TokenTree::Token(t, _) = tt else {
            panic!("unexpected token tree in type position");
        };
        match &t.kind {
            TokenKind::Comma => {}
            TokenKind::Ident(sym, _) if sym.as_str() == "result" => {
                steps.push(rty::TypePositionStep::Return);
            }
            TokenKind::Dollar => {
                let i = match iter.next() {
                    Some(TokenTree::Token(t, _)) => match &t.kind {
                        TokenKind::Literal(lit) => parse_int(lit),
                        _ => panic!("expected integer after `$` in type position: {:?}", t),
                    },
                    _ => panic!("expected integer after `$` in type position"),
                };
                steps.push(rty::TypePositionStep::Param(rty::FunctionParamIdx::from(i)));
            }
            TokenKind::Literal(lit) => {
                steps.push(rty::TypePositionStep::TypeArg(parse_int(lit)));
            }
            _ => panic!("unexpected token in type position: {:?}", t),
        }
    }

    rty::TypePosition::new(steps)
}

/// The paths a `#[thrust::reveal(a::b::f, ..)]` names, each as its segments; `None` for the bare
/// `#[thrust::reveal]`, and `Err` with a message for any other form (`= ..`, brackets or braces) or
/// for tokens that are not comma-separated paths (a leading or trailing `::` included).
pub fn reveal_paths(attr: &Attribute) -> Result<Option<Vec<Vec<Symbol>>>, String> {
    use rustc_ast::token::{Delimiter, TokenKind};
    use rustc_ast::tokenstream::TokenTree;

    let form = "`#[thrust::reveal]` is bare or takes paths in parentheses, separated by commas: `#[thrust::reveal(path::to::f, ..)]`";
    let Attribute::Unparsed(item) = attr else {
        return Ok(None);
    };
    let d = match &item.args {
        rustc_hir::AttrArgs::Empty => return Ok(None),
        rustc_hir::AttrArgs::Delimited(d) if d.delim == Delimiter::Parenthesis => d,
        _ => return Err(form.to_owned()),
    };
    let mut paths: Vec<Vec<Symbol>> = vec![Vec::new()];
    // Whether the next token must be a segment: at the start of a path and after `::`.
    let mut want_segment = true;
    for tree in d.tokens.iter() {
        let TokenTree::Token(token, _) = tree else {
            return Err(form.to_owned());
        };
        match (token.kind, want_segment) {
            (TokenKind::Ident(name, _), true) => {
                paths.last_mut().unwrap().push(name);
                want_segment = false;
            }
            (TokenKind::PathSep, false) => want_segment = true,
            (TokenKind::Comma, false) => {
                paths.push(Vec::new());
                want_segment = true;
            }
            _ => return Err(form.to_owned()),
        }
    }
    if want_segment && !paths.last().unwrap().is_empty() {
        return Err(form.to_owned());
    }
    paths.retain(|p| !p.is_empty());
    if paths.is_empty() {
        return Err("`#[thrust::reveal(..)]` names no function; write `#[thrust::reveal]` for the opaque functions of the module".to_owned());
    }
    Ok(Some(paths))
}

/// Whether `def_id` carries the attribute at `path` (one of the `*_path` functions above).
pub fn has_thrust_attr(tcx: TyCtxt<'_>, def_id: DefId, path: &[Symbol]) -> bool {
    tcx.get_attrs_by_path(def_id, path).next().is_some()
}
