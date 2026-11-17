//! The code between a `block_requires!` and the `block_ensures!` after it, which the code around
//! it reads through the contract, as it reads a call to a function with a written contract.
//!
//! The opening block, which ends in the `block_requires!` marker, goes on to the code under the
//! contract, whose first block has the `requires` formula as its whole precondition: the code
//! is checked once from there, and the `block_ensures!` marker checks the `ensures` formula and
//! ends the path. The opening block also goes on to the block after the contract, past the code,
//! with each local the code may change given a fresh value and the `ensures` formula assumed, as
//! a call's result and its `&mut` arguments are given in RustHorn. The other locals keep the
//! values and the facts they had at the opening, which is the frame of the contract.

use std::collections::{BTreeMap, HashSet};

use rustc_middle::mir::visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{self, BasicBlock, Body, Local, TerminatorKind};

use crate::analyze;
use crate::analyze::basic_block::{formula_marker_call, FormulaMarker};

/// A local the code under a contract may change.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Change {
    /// Assigned, moved, borrowed mutably or dropped as a whole or in a part of its own.
    Whole,
    /// Written only through a dereference of it: a `&mut` keeps its final value.
    ThroughDeref,
}

#[derive(Debug, Clone)]
pub struct BlockContract {
    /// The block that ends in the `block_requires!` marker call.
    pub opening: BasicBlock,
    /// The first block of the code under the contract, the opening marker's target.
    pub entry: BasicBlock,
    /// The block that ends in the `block_ensures!` marker call.
    pub closing: BasicBlock,
    /// The block after the contract, the closing marker's target.
    pub exit: BasicBlock,
    /// The blocks of the code under the contract, from `entry` to `closing`.
    pub blocks: HashSet<BasicBlock>,
    /// The locals the code under the contract may change.
    pub changed: BTreeMap<Local, Change>,
}

fn marker_of<'tcx>(
    ctx: &analyze::Analyzer<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
) -> Option<FormulaMarker> {
    let TerminatorKind::Call { func, args, .. } = &body.basic_blocks[bb].terminator().kind else {
        return None;
    };
    formula_marker_call(ctx, &body.local_decls, func, args).map(|(marker, ..)| marker)
}

/// Puts a block of its own between each `block_requires!` marker call and its target where the
/// target is reached from elsewhere too, such as the head of a loop the code under the contract
/// starts with, so that the first block under the contract is entered only from the marker.
pub fn separate_entries<'tcx>(ctx: &analyze::Analyzer<'tcx>, body: &mut Body<'tcx>) {
    let openings: Vec<BasicBlock> = body
        .basic_blocks
        .indices()
        .filter(|&bb| {
            !body.basic_blocks[bb].is_cleanup
                && marker_of(ctx, body, bb) == Some(FormulaMarker::BlockRequires)
        })
        .collect();
    for opening in openings {
        let terminator = body.basic_blocks[opening].terminator();
        let TerminatorKind::Call {
            target: Some(target),
            ..
        } = terminator.kind
        else {
            unreachable!("a marker call returns");
        };
        if !analyze::basic_block::needs_own_precondition(body, target) {
            continue;
        }
        let source_info = terminator.source_info;
        let entry = body.basic_blocks_mut().push(mir::BasicBlockData::new(
            Some(mir::Terminator {
                source_info,
                kind: TerminatorKind::Goto { target },
            }),
            false,
        ));
        let TerminatorKind::Call { target, .. } =
            &mut body.basic_blocks_mut()[opening].terminator_mut().kind
        else {
            unreachable!("a marker call returns");
        };
        *target = Some(entry);
    }
}

/// The block contracts of `body`. Stops at a `block_requires!` whose code can be left other
/// than through one `block_ensures!`, and at a `block_ensures!` that closes none.
pub fn collect<'tcx>(ctx: &analyze::Analyzer<'tcx>, body: &Body<'tcx>) -> Vec<BlockContract> {
    let mut contracts = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if data.is_cleanup || marker_of(ctx, body, bb) != Some(FormulaMarker::BlockRequires) {
            continue;
        }
        contracts.push(contract_opened_at(ctx, body, bb));
    }
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if !data.is_cleanup
            && marker_of(ctx, body, bb) == Some(FormulaMarker::BlockEnsures)
            && !contracts.iter().any(|contract| contract.closing == bb)
        {
            ctx.tcx.dcx().span_fatal(
                data.terminator().source_info.span,
                "`block_ensures!` closes no `block_requires!`",
            );
        }
    }
    contracts
}

fn contract_opened_at<'tcx>(
    ctx: &analyze::Analyzer<'tcx>,
    body: &Body<'tcx>,
    opening: BasicBlock,
) -> BlockContract {
    let terminator = body.basic_blocks[opening].terminator();
    let span = terminator.source_info.span;
    let fatal = |msg: &str| -> ! { ctx.tcx.dcx().span_fatal(span, msg.to_string()) };
    let TerminatorKind::Call {
        target: Some(entry),
        ..
    } = terminator.kind
    else {
        unreachable!("a marker call returns");
    };
    assert!(
        !analyze::basic_block::needs_own_precondition(body, entry),
        "the code under a block contract starts at a block of its own (`separate_entries`)"
    );

    let mut blocks = HashSet::new();
    let mut closings = Vec::new();
    let mut stack = vec![entry];
    while let Some(bb) = stack.pop() {
        if !blocks.insert(bb) {
            continue;
        }
        if bb == opening {
            fatal("a path from `block_requires!` comes back to it before a `block_ensures!`");
        }
        match marker_of(ctx, body, bb) {
            Some(FormulaMarker::BlockEnsures) => {
                closings.push(bb);
                continue;
            }
            Some(FormulaMarker::BlockRequires) => {
                fatal("a block contract inside another block contract is not supported")
            }
            _ => {}
        }
        let terminator = body.basic_blocks[bb].terminator();
        if matches!(
            terminator.kind,
            TerminatorKind::Return | TerminatorKind::Yield { .. } | TerminatorKind::CoroutineDrop
        ) {
            fatal("a path from `block_requires!` leaves the function before a `block_ensures!`");
        }
        stack.extend(
            terminator
                .successors()
                .filter(|succ| !body.basic_blocks[*succ].is_cleanup),
        );
    }
    let closing = match closings.as_slice() {
        [closing] => *closing,
        [] => fatal("no `block_ensures!` follows `block_requires!` on a path that returns"),
        _ => fatal("several `block_ensures!` close one `block_requires!`"),
    };
    let TerminatorKind::Call {
        target: Some(exit), ..
    } = body.basic_blocks[closing].terminator().kind
    else {
        unreachable!("a marker call returns");
    };
    if blocks.contains(&exit) {
        fatal("the code after `block_ensures!` is also under its contract");
    }

    let mut changed = ChangedLocals::default();
    for &bb in &blocks {
        let data = &body.basic_blocks[bb];
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = mir::Location {
                block: bb,
                statement_index,
            };
            changed.visit_statement(statement, location);
        }
        if bb != closing {
            let location = mir::Location {
                block: bb,
                statement_index: data.statements.len(),
            };
            changed.visit_terminator(data.terminator(), location);
        }
    }
    BlockContract {
        opening,
        entry,
        closing,
        exit,
        blocks,
        changed: changed.0,
    }
}

/// The locals a piece of code may change: the base local of every place it writes, borrows
/// mutably, moves or drops.
#[derive(Default)]
struct ChangedLocals(BTreeMap<Local, Change>);

impl<'tcx> Visitor<'tcx> for ChangedLocals {
    fn visit_place(&mut self, place: &mir::Place<'tcx>, context: PlaceContext, _: mir::Location) {
        let changes = match context {
            PlaceContext::MutatingUse(MutatingUseContext::Retag) => false,
            PlaceContext::MutatingUse(_) => true,
            PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => true,
            PlaceContext::NonMutatingUse(_) | PlaceContext::NonUse(_) => false,
        };
        if !changes {
            return;
        }
        let change = match place.projection.first() {
            Some(mir::ProjectionElem::Deref) => Change::ThroughDeref,
            _ => Change::Whole,
        };
        let entry = self.0.entry(place.local).or_insert(change);
        if change == Change::Whole {
            *entry = Change::Whole;
        }
    }
}

/// `body` with each contract's closing marker call going nowhere, so that the liveness of the
/// code under a contract is that of the code and the `ensures` formula alone: a local neither
/// uses is no parameter of its blocks, as a variable a helper function is not passed is not one
/// of its parameters.
pub fn body_ending_at_closings<'tcx>(
    mut body: Body<'tcx>,
    contracts: &[BlockContract],
) -> Body<'tcx> {
    for contract in contracts {
        let terminator = body.basic_blocks.as_mut()[contract.closing].terminator_mut();
        let TerminatorKind::Call { target, unwind, .. } = &mut terminator.kind else {
            unreachable!("a closing block ends in the marker call");
        };
        *target = None;
        *unwind = mir::UnwindAction::Unreachable;
    }
    body
}
