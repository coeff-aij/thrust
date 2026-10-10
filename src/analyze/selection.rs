//! The selection of `#![thrust::verify_only(..)]`: the functions whose bodies are checked when
//! only part of a crate is verified.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, CRATE_DEF_ID};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::{kw, Symbol};

use crate::analyze;

/// One entry of `#![thrust::verify_only(..)]`, a path relative to the crate root.
///
/// `m` selects the items defined directly in module `m`, `m::**` those of `m` and of all its
/// submodules, and `m::f`, `m::Type` or `m::Type::method` the named item with everything defined
/// inside it.
#[derive(Debug)]
struct Entry {
    segments: Vec<Symbol>,
    recursive: bool,
}

impl Entry {
    fn parse(entry: &str) -> Self {
        let mut segments: Vec<&str> = entry.split("::").filter(|s| !s.is_empty()).collect();
        let recursive = segments.last() == Some(&"**");
        if recursive {
            segments.pop();
        }
        if segments.first() == Some(&"crate") {
            segments.remove(0);
        }
        Entry {
            segments: segments.into_iter().map(Symbol::intern).collect(),
            recursive,
        }
    }

    fn selects(&self, path: &ItemPath) -> bool {
        let module = &path.segments[..path.module_len];
        if self.recursive {
            return module.starts_with(&self.segments);
        }
        module == self.segments.as_slice()
            || (self.segments.len() > path.module_len && path.segments.starts_with(&self.segments))
    }
}

/// The path of an item for the selection: its def path from the crate root, with an impl block
/// named by its self type, and the length of the path of the module that contains it.
struct ItemPath {
    segments: Vec<Symbol>,
    module_len: usize,
}

impl ItemPath {
    fn of(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let mut ancestors = Vec::new();
        let mut current = def_id;
        while let Some(parent) = tcx.opt_parent(current) {
            ancestors.push(current);
            current = parent;
        }
        let mut path = ItemPath {
            segments: Vec::new(),
            module_len: 0,
        };
        for id in ancestors.into_iter().rev() {
            let segment = match tcx.def_kind(id) {
                DefKind::Impl { .. } => impl_self_name(tcx, id),
                _ => tcx.opt_item_name(id).unwrap_or(kw::Underscore),
            };
            path.segments.push(segment);
            if tcx.def_kind(id) == DefKind::Mod {
                path.module_len = path.segments.len();
            }
        }
        path
    }
}

fn impl_self_name(tcx: TyCtxt<'_>, impl_def_id: DefId) -> Symbol {
    tcx.type_of(impl_def_id)
        .instantiate_identity()
        .ty_adt_def()
        .map(|adt| tcx.item_name(adt.did()))
        .unwrap_or_else(|| Symbol::intern("{impl}"))
}

#[derive(Debug)]
pub struct Selection {
    entries: Vec<Entry>,
}

impl Selection {
    /// The union of the crate's `#![thrust::verify_only(..)]` attributes, if it has any.
    pub fn of_crate(tcx: TyCtxt<'_>) -> Option<Self> {
        use rustc_ast::token::{LitKind, Token, TokenKind};
        use rustc_ast::tokenstream::TokenTree;

        let path = analyze::annot::verify_only_path();
        let attrs: Vec<_> = tcx
            .get_attrs_by_path(CRATE_DEF_ID.to_def_id(), &path)
            .collect();
        if attrs.is_empty() {
            return None;
        }
        let mut entries = Vec::new();
        for attr in attrs {
            for tt in analyze::annot::extract_annot_tokens(attr.clone()).iter() {
                match tt {
                    TokenTree::Token(
                        Token {
                            kind: TokenKind::Literal(lit),
                            ..
                        },
                        _,
                    ) if lit.kind == LitKind::Str => {
                        entries.push(Entry::parse(lit.symbol.as_str()));
                    }
                    TokenTree::Token(
                        Token {
                            kind: TokenKind::Comma,
                            ..
                        },
                        _,
                    ) => {}
                    _ => panic!("verify_only takes string literals: {tt:?}"),
                }
            }
        }
        Some(Selection { entries })
    }

    pub fn contains(&self, tcx: TyCtxt<'_>, def_id: DefId) -> bool {
        let path = ItemPath::of(tcx, def_id);
        self.entries.iter().any(|entry| entry.selects(&path))
    }

    /// Whether the selection contains `law_def_id` as inherited by the impl `impl_def_id`, which
    /// is named as a method of the impl.
    pub fn contains_inherited(
        &self,
        tcx: TyCtxt<'_>,
        impl_def_id: DefId,
        law_def_id: DefId,
    ) -> bool {
        let mut path = ItemPath::of(tcx, impl_def_id);
        path.segments.push(tcx.item_name(law_def_id));
        self.entries.iter().any(|entry| entry.selects(&path))
    }
}
