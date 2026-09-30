//! Structs declared `#[thrust::opaque]`, whose model is an abstraction of their fields rather
//! than the fields themselves.
//!
//! The translation of a field access or a struct literal reads the model by position, so only a
//! body that is not analyzed may reach into the fields of such a struct. Every model value of it
//! is then produced and consumed by trusted contracts.

use rustc_middle::mir::{self, visit::PlaceContext, visit::Visitor, Location};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::def_id::DefId;
use rustc_span::{Span, Symbol};

use crate::analyze;
use crate::rty;

pub fn is_opaque(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.get_attrs_by_path(def_id, &analyze::annot::opaque_path())
        .next()
        .is_some()
}

fn opaque_struct<'tcx>(tcx: TyCtxt<'tcx>, ty: mir_ty::Ty<'tcx>) -> Option<mir_ty::AdtDef<'tcx>> {
    let mir_ty::TyKind::Adt(def, _) = ty.kind() else {
        return None;
    };
    (def.is_struct() && is_opaque(tcx, def.did())).then_some(*def)
}

/// A statement of a body that reaches into the fields of an opaque struct.
pub struct FieldAccess<'tcx> {
    pub span: Span,
    pub adt: mir_ty::AdtDef<'tcx>,
    /// The field read or written; `None` for a struct literal, which sets them all.
    pub field: Option<Symbol>,
}

impl FieldAccess<'_> {
    pub fn describe(&self, tcx: TyCtxt<'_>) -> String {
        let ty = tcx.def_path_str(self.adt.did());
        match self.field {
            Some(field) => format!("accesses the field `{field}` of the opaque type `{ty}`"),
            None => format!("builds the opaque type `{ty}` from its fields"),
        }
    }
}

pub fn field_accesses<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> Vec<FieldAccess<'tcx>> {
    let mut collector = FieldAccessCollector {
        tcx,
        body,
        found: Vec::new(),
    };
    collector.visit_body(body);
    collector.found
}

struct FieldAccessCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    found: Vec<FieldAccess<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for FieldAccessCollector<'_, 'tcx> {
    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, location: Location) {
        if !context.is_use() {
            return;
        }
        let mut base = mir::PlaceTy::from_ty(self.body.local_decls[place.local].ty);
        for elem in place.projection {
            if let mir::ProjectionElem::Field(idx, _) = elem {
                if let Some(adt) = opaque_struct(self.tcx, base.ty) {
                    self.found.push(FieldAccess {
                        span: self.body.source_info(location).span,
                        adt,
                        field: Some(adt.non_enum_variant().fields[idx].name),
                    });
                }
            }
            base = base.projection_ty(self.tcx, elem);
        }
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        if let mir::Rvalue::Aggregate(kind, _) = rvalue {
            if let mir::AggregateKind::Adt(def_id, ..) = **kind {
                let ty = self.tcx.type_of(def_id).instantiate_identity();
                if let Some(adt) = opaque_struct(self.tcx, ty) {
                    self.found.push(FieldAccess {
                        span: self.body.source_info(location).span,
                        adt,
                        field: None,
                    });
                }
            }
        }
        self.super_rvalue(rvalue, location);
    }

    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, _location: Location) {
        if let Some(adt) = opaque_struct_in_value(self.tcx, constant.const_.ty()) {
            self.found.push(FieldAccess {
                span: constant.span,
                adt,
                field: None,
            });
        }
    }
}

/// An opaque struct that a constant of type `ty` may contain, and that the translation of the
/// constant would build from its fields.
fn opaque_struct_in_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: mir_ty::Ty<'tcx>,
) -> Option<mir_ty::AdtDef<'tcx>> {
    match ty.kind() {
        mir_ty::TyKind::Adt(_, args) => opaque_struct(tcx, ty)
            .or_else(|| args.types().find_map(|t| opaque_struct_in_value(tcx, t))),
        mir_ty::TyKind::Tuple(tys) => tys.iter().find_map(|t| opaque_struct_in_value(tcx, t)),
        mir_ty::TyKind::Array(t, _) | mir_ty::TyKind::Slice(t) | mir_ty::TyKind::Ref(_, t, _) => {
            opaque_struct_in_value(tcx, *t)
        }
        _ => None,
    }
}

fn mentions<'tcx>(ty: mir_ty::Ty<'tcx>, adt: DefId) -> bool {
    ty.walk().any(|arg| {
        arg.as_type()
            .is_some_and(|t| matches!(t.kind(), mir_ty::TyKind::Adt(def, _) if def.did() == adt))
    })
}

/// Whether the contract `fn_ty` of a function with signature `sig` constrains a value whose
/// type contains the struct `adt`.
pub fn contract_states_model<'tcx>(
    fn_ty: &rty::FunctionType,
    sig: &mir_ty::FnSig<'tcx>,
    adt: DefId,
) -> bool {
    let param_mentions = |idx: rty::FunctionParamIdx| {
        sig.inputs()
            .get(idx.index())
            .is_some_and(|ty| mentions(*ty, adt))
    };
    let ret_mentions = mentions(sig.output(), adt);
    let states = |refinement: &rty::Refinement<rty::FunctionParamIdx>, value_mentions: bool| {
        refinement.body.fv().any(|v| match v {
            rty::RefinedTypeVar::Value => value_mentions,
            rty::RefinedTypeVar::Free(idx) => param_mentions(*idx),
            rty::RefinedTypeVar::Existential(_) => false,
        })
    };
    fn_ty
        .params
        .iter_enumerated()
        .any(|(idx, param)| states(&param.refinement, param_mentions(idx)))
        || states(&fn_ty.ret.refinement, ret_mentions)
}
