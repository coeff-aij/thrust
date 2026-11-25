//! What a loop with a written invariant keeps of what held when it was entered.
//!
//! A loop head with a written invariant has the invariant as its precondition, so nothing the
//! code before the loop established about a variable the invariant does not name would survive
//! into the loop. The head instead keeps what held on entry of each variable the loop does not
//! change, as a verifier that havocs only the variables a loop assigns does.
//!
//! A block of its own, the landing, is put on the edge into the head from outside the loop. It
//! inherits the state before the loop, which is its precondition. Every block of the loop that
//! has a precondition of its own assumes the landing's precondition over the entry values of the
//! unchanged variables, the other values left unknown. A variable the loop does not write is its
//! own entry value in a block that has it as a parameter; a block without it carries the
//! landing's value as an extra parameter, the entry snapshot, passed on unchanged inside the
//! loop. For a `&mut` the loop writes through, the snapshot is of the final value alone, the only
//! part the loop leaves as it was; a block that has the `&mut` requires its final value to equal
//! the snapshot, which every edge into it checks. That precondition is the premise of the clause
//! that enters the loop and has no unknown of its own, and an entry value is never changed, so
//! the assumption holds at every visit and needs no check.

use std::collections::{BTreeMap, HashSet};

use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

use crate::analyze::block_contract::{changed_locals, BlockContract, Change};
use crate::chc;
use crate::refine::{final_value_term, final_value_type};
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
    /// The type of the entry snapshot of a variable of type `ty`: the variable's own type for
    /// [`Kept::Whole`], and for [`Kept::FinalOnly`] the type of the final value of the `&mut`,
    /// which is all the loop leaves as it was.
    pub fn snapshot_type(self, ty: rty::Type<rty::Closed>) -> rty::Type<rty::Closed> {
        match self {
            Kept::Whole => ty,
            Kept::FinalOnly => final_value_type(&ty),
        }
    }

    /// What a block of the loop requires of the parameter `current` holding the variable, as a
    /// refinement of its entry snapshot, or `None` when the block needs none: a variable the loop
    /// does not write, which the block has as a parameter itself, is its own entry snapshot.
    pub fn requirement_on_snapshot(
        self,
        current: rty::FunctionParamIdx,
        current_ty: &rty::Type<rty::FunctionParamIdx>,
    ) -> Option<rty::Refinement<rty::FunctionParamIdx>> {
        match self {
            Kept::Whole => None,
            Kept::FinalOnly => {
                let snapshot = chc::Term::var(rty::RefinedTypeVar::Value);
                let current = final_value_term(
                    current_ty,
                    chc::Term::var(rty::RefinedTypeVar::Free(current)),
                );
                Some(snapshot.equal_to(current).into())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct LoopFrame {
    /// The head of the loop.
    pub head: BasicBlock,
    /// The block on the edge into the head from outside the loop.
    pub landing: BasicBlock,
    /// The block of the original body that jumped to the head, before the landing was put in.
    pub source: BasicBlock,
    /// The blocks of the loop that run, the head included.
    pub blocks: HashSet<BasicBlock>,
    /// The locals the loop leaves as they were.
    pub kept: BTreeMap<Local, Kept>,
}

/// What the report keeps of the entry into a loop: its head, and the block of the original body
/// that jumps to it.
#[derive(Debug, Clone, Copy)]
pub struct LoopEntry {
    pub head: BasicBlock,
    pub source: BasicBlock,
}

impl LoopFrame {
    /// The blocks of the loop that carry its entry snapshot, in order. The code under a block
    /// contract inside the loop is left out: it starts from the contract's `requires` alone and
    /// is not entered from the loop's blocks other than through the contract, which the code
    /// after it passes over with the snapshot of the block that opens it.
    pub fn snapshot_blocks(&self, contracts: &[BlockContract]) -> Vec<BasicBlock> {
        let mut blocks: Vec<_> = self
            .blocks
            .iter()
            .copied()
            .filter(|bb| {
                !contracts.iter().any(|contract| {
                    contract.blocks.contains(bb) && !contract.blocks.contains(&self.head)
                })
            })
            .collect();
        blocks.sort();
        blocks
    }
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

/// The blocks of the natural loop of `head` that run, or `None` if `head` heads no loop.
fn running_blocks(body: &Body<'_>, head: BasicBlock) -> Option<HashSet<BasicBlock>> {
    let blocks = natural_loop(body, head)?;
    Some(
        blocks
            .into_iter()
            .filter(|&bb| !body.basic_blocks[bb].is_cleanup)
            .collect(),
    )
}

/// Puts a landing block on the edge into each of `heads` from outside its loop, and returns the
/// frames of the loops that have exactly one such edge.
///
/// Every landing is put in before any frame is computed, so that the blocks of a loop include the
/// landings of the loops nested in it.
pub fn separate_entries<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    heads: impl IntoIterator<Item = BasicBlock>,
) -> Vec<LoopFrame> {
    let mut heads: Vec<_> = heads.into_iter().collect();
    heads.sort();
    let landings: Vec<_> = heads
        .into_iter()
        .filter_map(|head| {
            let (landing, source) = put_landing_before(body, head)?;
            Some((head, landing, source))
        })
        .collect();
    landings
        .into_iter()
        .map(|(head, landing, source)| {
            let blocks = running_blocks(body, head).expect("a head with a landing heads a loop");
            let kept = kept_locals(tcx, body, &blocks);
            LoopFrame {
                head,
                landing,
                source,
                blocks,
                kept,
            }
        })
        .collect()
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

/// Puts a landing on the edge into `head` from outside its loop, when there is one such edge only.
fn put_landing_before<'tcx>(
    body: &mut Body<'tcx>,
    head: BasicBlock,
) -> Option<(BasicBlock, BasicBlock)> {
    let blocks = running_blocks(body, head)?;
    let outside = outside_entry(body, head, &blocks)?;
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
    Some((landing, outside))
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
