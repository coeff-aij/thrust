//! The selection of `THRUST_VERIFY_ONLY`: the functions whose bodies are checked when only part
//! of a crate is verified.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::{kw, Symbol};

/// One entry of `THRUST_VERIFY_ONLY`, a path relative to the crate root.
///
/// `m` selects the items defined directly in module `m`, `m::**` those of `m` and of all its
/// submodules, and `m::f`, `m::Type` or `m::Type::method` the named item with everything defined
/// inside it.
#[derive(Debug)]
struct Entry {
    segments: Vec<Symbol>,
    recursive: bool,
    text: String,
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
            text: entry.to_owned(),
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
pub struct ItemPath {
    segments: Vec<Symbol>,
    module_len: usize,
}

impl ItemPath {
    pub fn of(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
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

    /// The path of `law_def_id` as inherited by the impl `impl_def_id`, named as a method of the
    /// impl.
    pub fn of_inherited(tcx: TyCtxt<'_>, impl_def_id: DefId, law_def_id: DefId) -> Self {
        let mut path = ItemPath::of(tcx, impl_def_id);
        path.segments.push(tcx.item_name(law_def_id));
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

/// Whether the selection applies to the crate being compiled: under cargo only to the packages
/// it was asked to build, not to their dependencies; otherwise to the one crate compiled.
fn applies_to_crate(compiled_by_cargo: bool, primary: bool) -> bool {
    !compiled_by_cargo || primary
}

#[derive(Debug)]
pub struct Selection {
    entries: Vec<Entry>,
}

impl Selection {
    /// The entries of `THRUST_VERIFY_ONLY`, a comma-separated list, if it is set and not empty
    /// and the crate being compiled is the one to verify.
    pub fn from_env() -> Option<Self> {
        Self::from_var("THRUST_VERIFY_ONLY")
    }

    /// The entries of the environment variable `var`, read as `THRUST_VERIFY_ONLY` is.
    pub fn from_var(var: &str) -> Option<Self> {
        let compiled_by_cargo = std::env::var_os("CARGO_CRATE_NAME").is_some();
        let primary = std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some();
        if !applies_to_crate(compiled_by_cargo, primary) {
            return None;
        }
        let value = std::env::var(var).ok()?;
        let entries: Vec<_> = value
            .split(',')
            .map(str::trim)
            .filter(|entry| !entry.is_empty())
            .map(Entry::parse)
            .collect();
        if entries.is_empty() {
            return None;
        }
        Some(Selection { entries })
    }

    pub fn contains(&self, tcx: TyCtxt<'_>, def_id: DefId) -> bool {
        let path = ItemPath::of(tcx, def_id);
        self.entries.iter().any(|entry| entry.selects(&path))
    }

    /// Whether the selection contains `law_def_id` as inherited by the impl `impl_def_id`.
    pub fn contains_inherited(
        &self,
        tcx: TyCtxt<'_>,
        impl_def_id: DefId,
        law_def_id: DefId,
    ) -> bool {
        let path = ItemPath::of_inherited(tcx, impl_def_id, law_def_id);
        self.entries.iter().any(|entry| entry.selects(&path))
    }

    /// Reports each entry that selects none of `paths`, which would leave its intended part of
    /// the crate unverified without a sign.
    pub fn report_unmatched(&self, tcx: TyCtxt<'_>, paths: &[ItemPath]) {
        for entry in &self.entries {
            if !paths.iter().any(|path| entry.selects(path)) {
                tcx.dcx().err(format!(
                    "`THRUST_VERIFY_ONLY` entry `{}` selects no function",
                    entry.text
                ));
            }
        }
    }
}
