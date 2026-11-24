//! What a loop with a written invariant keeps of what held when it was entered.
//!
//! A loop head with a written invariant has the invariant as its precondition, so nothing the
//! code before the loop established about a variable the invariant does not name would survive
//! into the loop. The head instead keeps what held on entry of each variable the loop does not
//! change, as a verifier that havocs only the variables a loop assigns does.
//!
//! A block of its own, the landing, is put on the edge into the head from outside the loop. It
//! inherits the state before the loop, which is its precondition. Every block of the loop that
//! has a precondition of its own carries the landing's values of the unchanged variables as
//! extra parameters, the entry snapshot, passed on unchanged inside the loop. Such a block
//! requires each unchanged variable to equal its snapshot, which every edge into it checks, and
//! assumes the landing's precondition over the snapshot. That precondition is the premise of
//! the clause that enters the loop and has no unknown of its own, and a snapshot is never
//! changed, so the assumption holds at every visit and needs no check.

use std::collections::{BTreeMap, HashSet};

use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

use crate::analyze::block_contract::{changed_locals, Change};
use crate::chc;
use crate::rty;

/// How much of a variable the loop leaves as it was.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kept {
    /// The whole value.
    Whole,
    /// The final value of a `&mut`, which the loop writes through but does not reborrow or move.
    FinalOnly,
}

impl Kept {
    /// What a block of the loop requires of the parameter `current` holding the variable, as a
    /// refinement of its entry snapshot.
    pub fn equality_with(
        self,
        current: rty::FunctionParamIdx,
    ) -> rty::Refinement<rty::FunctionParamIdx> {
        let snapshot = chc::Term::var(rty::RefinedTypeVar::Value);
        let current = chc::Term::var(rty::RefinedTypeVar::Free(current));
        match self {
            Kept::Whole => snapshot.equal_to(current).into(),
            Kept::FinalOnly => snapshot.mut_final().equal_to(current.mut_final()).into(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopFrame {
    /// The head of the loop.
    pub head: BasicBlock,
    /// The block on the edge into the head from outside the loop.
    pub landing: BasicBlock,
    /// The blocks of the loop that run, the head included.
    pub blocks: HashSet<BasicBlock>,
    /// The locals the loop leaves as they were.
    pub kept: BTreeMap<Local, Kept>,
}

/// The blocks of the natural loop whose head is `head`, or `None` if `head` heads no loop.
pub fn natural_loop(body: &Body<'_>, head: BasicBlock) -> Option<HashSet<BasicBlock>> {
    let dominators = body.basic_blocks.dominators();
    let preds = body.basic_blocks.predecessors();
    let mut pending: Vec<_> = preds[head]
        .iter()
        .copied()
        .filter(|&p| dominators.dominates(head, p))
        .collect();
    if pending.is_empty() {
        return None;
    }
    let mut blocks = HashSet::from([head]);
    while let Some(b) = pending.pop() {
        if blocks.insert(b) {
            pending.extend(preds[b].iter().copied());
        }
    }
    Some(blocks)
}

/// Puts a landing block on the edge into each of `heads` from outside its loop, and returns the
/// frames of the loops that have exactly one such edge.
pub fn separate_entries<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    heads: impl IntoIterator<Item = BasicBlock>,
) -> Vec<LoopFrame> {
    let mut heads: Vec<_> = heads.into_iter().collect();
    heads.sort();
    heads
        .into_iter()
        .filter_map(|head| frame_of(tcx, body, head))
        .collect()
}

fn frame_of<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>, head: BasicBlock) -> Option<LoopFrame> {
    let blocks: HashSet<_> = natural_loop(body, head)?
        .into_iter()
        .filter(|&bb| !body.basic_blocks[bb].is_cleanup)
        .collect();
    let outside = outside_entry(body, head, &blocks)?;
    let landing = put_landing_before(body, head, outside);
    let kept = kept_locals(tcx, body, &blocks);
    Some(LoopFrame {
        head,
        landing,
        blocks,
        kept,
    })
}

/// The block that jumps to `head` from outside its loop, when there is one such edge only.
fn outside_entry(
    body: &Body<'_>,
    head: BasicBlock,
    blocks: &HashSet<BasicBlock>,
) -> Option<BasicBlock> {
    if head == mir::START_BLOCK {
        return None;
    }
    let mut outside = body.basic_blocks.predecessors()[head]
        .iter()
        .copied()
        .filter(|pred| !blocks.contains(pred));
    let (Some(pred), None) = (outside.next(), outside.next()) else {
        return None;
    };
    let edges = body.basic_blocks[pred]
        .terminator()
        .successors()
        .filter(|&succ| succ == head)
        .count();
    (edges == 1 && !body.basic_blocks[pred].is_cleanup).then_some(pred)
}

fn put_landing_before<'tcx>(
    body: &mut Body<'tcx>,
    head: BasicBlock,
    outside: BasicBlock,
) -> BasicBlock {
    let source_info = body.basic_blocks[outside].terminator().source_info;
    let landing = body.basic_blocks_mut().push(mir::BasicBlockData::new(
        Some(mir::Terminator {
            source_info,
            kind: mir::TerminatorKind::Goto { target: head },
        }),
        false,
    ));
    body.basic_blocks_mut()[outside]
        .terminator_mut()
        .successors_mut(|target| {
            if *target == head {
                *target = landing;
            }
        });
    landing
}

/// The locals of `body` that the code of `blocks` leaves as they were: those it does not write,
/// borrow mutably, move or drop, and the `&mut`s it writes only through.
fn kept_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    blocks: &HashSet<BasicBlock>,
) -> BTreeMap<Local, Kept> {
    let changed = changed_locals(tcx, body, blocks, None);
    body.local_decls
        .iter_enumerated()
        .filter_map(|(local, decl)| {
            let kept = match changed.get(&local) {
                None => Kept::Whole,
                Some(Change::ThroughDeref)
                    if decl.ty.ref_mutability() == Some(mir_ty::Mutability::Mut) =>
                {
                    Kept::FinalOnly
                }
                Some(Change::Moved | Change::ThroughDeref | Change::Whole) => return None,
            };
            Some((local, kept))
        })
        .collect()
}
