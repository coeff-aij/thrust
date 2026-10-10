//! Turns each panicking path into a check that it is unreachable, without its payload.
//!
//! A panic entry point (`core::panicking::panic_fmt`, `assert_failed`, `std::rt::begin_panic`,
//! ...) takes a payload built from `fmt::Arguments`, which Thrust cannot type. The blocks from
//! which every path reaches such a call through only statements and calls to `core::fmt`
//! constructors are a panicking path: it is entered if and only if the panic happens, because
//! those constructors return without an observable effect. Each such block becomes
//! `assert(false)`, which requires the block to be unreachable, as the `panic` lang item's
//! signature does for `panic!()`, and its payload statements are dropped. Locals that no block
//! mentions any more are given the type `()`, so that their payload types are never built.

use rustc_middle::mir::{self, BasicBlock, BasicBlockData, Body, Local, Operand, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_span::{sym, Symbol};

fn in_module<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, module: Symbol) -> bool {
    tcx.def_path(def_id)
        .data
        .iter()
        .any(|elem| elem.data.get_opt_name() == Some(module))
}

fn is_panic_entry_point<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let krate = tcx.crate_name(def_id.krate);
    (krate == sym::core || krate == sym::std)
        && tcx
            .fn_sig(def_id)
            .skip_binder()
            .output()
            .skip_binder()
            .is_never()
        && in_module(tcx, def_id, sym::panicking)
}

fn is_payload_constructor<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    tcx.crate_name(def_id.krate) == sym::core && in_module(tcx, def_id, sym::fmt)
}

fn callee<'tcx>(func: &Operand<'tcx>) -> Option<DefId> {
    func.const_fn_def().map(|(def_id, _)| def_id)
}

fn panicking_blocks<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<BasicBlock> {
    let mut panicking = vec![false; body.basic_blocks.len()];
    loop {
        let mut changed = false;
        for (bb, data) in body.basic_blocks.iter_enumerated() {
            if panicking[bb.as_usize()] || data.is_cleanup {
                continue;
            }
            let is_panicking = match &data.terminator().kind {
                TerminatorKind::Goto { target } => panicking[target.as_usize()],
                TerminatorKind::Call {
                    func, target: None, ..
                } => callee(func).is_some_and(|def_id| is_panic_entry_point(tcx, def_id)),
                TerminatorKind::Call {
                    func,
                    target: Some(target),
                    ..
                } => {
                    panicking[target.as_usize()]
                        && callee(func).is_some_and(|def_id| is_payload_constructor(tcx, def_id))
                }
                _ => false,
            };
            if is_panicking {
                panicking[bb.as_usize()] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    body.basic_blocks
        .indices()
        .filter(|bb| panicking[bb.as_usize()])
        .collect()
}

fn mentioned_locals(body: &Body<'_>) -> Vec<bool> {
    struct Collector(Vec<bool>);
    impl<'tcx> mir::visit::Visitor<'tcx> for Collector {
        fn visit_local(&mut self, local: Local, _: mir::visit::PlaceContext, _: mir::Location) {
            self.0[local.as_usize()] = true;
        }
    }
    let mut collector = Collector(vec![false; body.local_decls.len()]);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        mir::visit::Visitor::visit_basic_block_data(&mut collector, bb, data);
    }
    collector.0
}

pub fn elide<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let panicking = panicking_blocks(tcx, body);
    if panicking.is_empty() {
        return;
    }
    let source_info = body.basic_blocks[panicking[0]].terminator().source_info;
    let unreachable = body.basic_blocks_mut().push(BasicBlockData::new(
        Some(mir::Terminator {
            source_info,
            kind: TerminatorKind::Unreachable,
        }),
        false,
    ));
    for bb in panicking {
        tracing::debug!(?bb, "panicking path");
        let data = &mut body.basic_blocks_mut()[bb];
        data.statements.clear();
        data.terminator_mut().kind = TerminatorKind::Assert {
            cond: Operand::Constant(Box::new(mir::ConstOperand {
                span: source_info.span,
                user_ty: None,
                const_: mir::Const::from_bool(tcx, false),
            })),
            expected: true,
            msg: Box::new(mir::AssertKind::NullPointerDereference),
            target: unreachable,
            unwind: mir::UnwindAction::Continue,
        };
    }
    let mentioned = mentioned_locals(body);
    let unmentioned: Vec<Local> = body
        .vars_and_temps_iter()
        .filter(|local| !mentioned[local.as_usize()])
        .collect();
    for local in unmentioned {
        body.local_decls[local].ty = tcx.types.unit;
    }
}
