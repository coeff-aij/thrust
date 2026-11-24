//! Creates each two-phase mutable borrow at its activation, as Creusot does
//! (`activate_two_phases` in `creusot/src/analysis.rs`).
//!
//! A two-phase borrow `_t = &mut P` (an autoref'd receiver, `x.bump(arg)`) only reserves `P`,
//! sharing it, until its activation, the unique use of `_t`; the code in between may read `P`.
//! Thrust replaces a borrowed place by the borrow's prophecy where the borrow is created, so every
//! two-phase borrow is created right before its activation; the deref temporaries rustc makes for
//! its place are already folded into the place by `unelaborate_derefs`. rustc evaluates `P` once,
//! at the reservation, and a write in between that may change a pointer `P` goes through or one of
//! its index locals is refused. Without one, `P` names the same memory at both points: the borrow
//! created at the activation is rustc's borrow, and the reads in between see the current value.
//! A write that reaches such a pointer only through an index (`(*s)[j] = b` while `*(*s)[i]` is
//! reserved) leaves `P` unchanged exactly when the two indices differ, so [`index_obligations`]
//! finds the pairs the analysis asserts different at the write. Thrust reads MIR without `InstSimplify`, which would turn a reborrow
//! `&mut *p` into `copy p` and lose its two-phase kind.
//!
//! The borrow of a slice element (`s[0].bump(s[1])`) is created at its activation by the
//! reconstruction of its `IndexMut::index_mut` call, which runs first and asks
//! [`creation_point`] where to create it.

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

use rustc_middle::mir::{
    self, visit::PlaceContext, BasicBlock, Body, Local, Location, Place, PlaceElem, PlaceRef,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

/// A two-phase borrow `temp = &mut place` made at `reservation`.
struct TwoPhaseBorrow<'tcx> {
    reservation: Location,
    temp: Local,
    place: Place<'tcx>,
}

/// The index pairs a write must keep different: `reserved` is the index of a reserved two-phase
/// borrow's place, `written` the index of the write at the statement spanning `write`.
///
/// They are keyed by span, not location, because the reconstruction of slice indexing and
/// [`move_to_activation`] move statements. The basic-block analysis asserts a pair where the
/// written index is still live: at the write, or at the indexing call the reconstruction made of
/// it, which has a span inside the write's.
#[derive(Clone, Default)]
pub struct IndexObligations {
    pairs: Vec<(Span, Local, Local)>,
    emitted: Rc<RefCell<HashSet<(Span, Local, Local)>>>,
}

impl IndexObligations {
    /// The obligations of writes whose span contains `span`, those of `written` only.
    pub fn at(&self, span: Span, written: impl Fn(Local) -> bool) -> Vec<(Span, Local, Local)> {
        let found = self
            .pairs
            .iter()
            .filter(|(write, _, w)| write.contains(span) && written(*w));
        found.copied().collect()
    }

    pub fn mark_emitted(&self, obligation: (Span, Local, Local)) {
        self.emitted.borrow_mut().insert(obligation);
    }

    /// Stops at an obligation the analysis did not assert, which would leave its write unchecked.
    pub fn require_all_emitted(&self, tcx: TyCtxt<'_>) {
        let emitted = self.emitted.borrow();
        if let Some(obligation) = self.pairs.iter().find(|o| !emitted.contains(o)) {
            tcx.dcx().span_fatal(
                obligation.0,
                "the index of this write to a place a two-phase mutable borrow goes through is \
                 not checked against the borrow's index",
            );
        }
    }
}

/// Finds, for each write between a reservation and its activation that reaches a pointer of the
/// borrowed place only through an index, the pair of index locals the analysis asserts different
/// at the write: then no write in between changes a pointer on the path, and the borrow created
/// at the activation is rustc's borrow. With equal indices the assertion fails and verification
/// stops. A write that is no statement (a call's destination) is refused.
pub fn index_obligations<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> IndexObligations {
    let mut obligations = IndexObligations::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for statement_index in 0..data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            let Some(borrow) = two_phase_borrow_at(body, location) else {
                continue;
            };
            let Some(activation) = activation(tcx, body, &borrow) else {
                continue;
            };
            for (write, reserved, written) in index_writes(tcx, body, &borrow, activation) {
                let in_statement =
                    write.statement_index < body.basic_blocks[write.block].statements.len();
                if !in_statement {
                    fatal_at(
                        tcx,
                        body,
                        write,
                        "a write that is no statement may change which place a two-phase mutable \
                         borrow names before the borrow is used",
                    );
                }
                let obligation = (body.source_info(write).span, reserved, written);
                if !obligations.pairs.contains(&obligation) {
                    obligations.pairs.push(obligation);
                }
            }
        }
    }
    obligations
}

/// The writes between the reservation and the activation whose overlap with the borrowed place is
/// decided by two index locals: the write's location, the reserved index and the written index.
fn index_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow: &TwoPhaseBorrow<'tcx>,
    activation: Location,
) -> Vec<(Location, Local, Local)> {
    let mut finder = AddressWriteFinder {
        tcx,
        body,
        addresses: address_places(borrow.place),
        write: None,
        obligations: Vec::new(),
    };
    for location in locations_between(body, borrow.reservation, activation) {
        visit_location(body, &mut finder, location);
    }
    finder.obligations
}

pub fn move_to_activation<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let mut moves = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for statement_index in 0..data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            let Some(borrow) = two_phase_borrow_at(body, location) else {
                continue;
            };
            let activation = checked_activation(tcx, body, &borrow);
            moves.push((borrow, activation));
        }
    }
    apply(body, moves);
}

/// Where the two-phase borrow made by the statement at `location` is created: its activation.
/// `None` when the statement is no two-phase borrow or the borrow is never used.
pub fn creation_point<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    location: Location,
) -> Option<Location> {
    let borrow = two_phase_borrow_at(body, location)?;
    checked_activation(tcx, body, &borrow)
}

fn two_phase_borrow_at<'tcx>(
    body: &Body<'tcx>,
    location: Location,
) -> Option<TwoPhaseBorrow<'tcx>> {
    let stmt = body.basic_blocks[location.block]
        .statements
        .get(location.statement_index)?;
    let (lhs, mir::Rvalue::Ref(_, kind, place)) = stmt.kind.as_assign()? else {
        return None;
    };
    if !kind.allows_two_phase_borrow() {
        return None;
    }
    let temp = lhs
        .as_local()
        .expect("two-phase borrow must assign to a local");
    Some(TwoPhaseBorrow {
        reservation: location,
        temp,
        place: *place,
    })
}

/// The activation of `borrow`, after refusing a write before it that may change which place the
/// borrow names. `None` when the borrow is never used.
fn checked_activation<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow: &TwoPhaseBorrow<'tcx>,
) -> Option<Location> {
    let activation = activation(tcx, body, borrow)?;
    refuse_address_writes(tcx, body, borrow, activation);
    Some(activation)
}

/// The unique use of the borrow's temporary, which the reservation dominates.
fn activation(tcx: TyCtxt<'_>, body: &Body<'_>, borrow: &TwoPhaseBorrow<'_>) -> Option<Location> {
    let uses: Vec<Location> = use_locations(body, borrow.temp)
        .into_iter()
        .filter(|location| *location != borrow.reservation)
        .collect();
    let dominators = body.basic_blocks.dominators();
    match uses.as_slice() {
        [] => None,
        [activation] if borrow.reservation.dominates(*activation, dominators) => Some(*activation),
        _ => fatal_at(
            tcx,
            body,
            borrow.reservation,
            "a two-phase mutable borrow that is not used exactly once after it is made is not supported",
        ),
    }
}

/// Stops at a write between the reservation and the activation that may change a pointer the
/// borrowed place goes through, or one of its index locals.
fn refuse_address_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow: &TwoPhaseBorrow<'tcx>,
    activation: Location,
) {
    let mut finder = AddressWriteFinder {
        tcx,
        body,
        addresses: address_places(borrow.place),
        write: None,
        obligations: Vec::new(),
    };
    for location in locations_between(body, borrow.reservation, activation) {
        visit_location(body, &mut finder, location);
        let Some(write) = finder.write else {
            continue;
        };
        tcx.dcx()
            .struct_span_fatal(
                body.source_info(write).span,
                "this write may change which place a two-phase mutable borrow names before the \
                 borrow is used; Thrust supports such a borrow only while the pointers and \
                 indices its place goes through are unchanged",
            )
            .with_span_note(
                body.source_info(borrow.reservation).span,
                "the borrow is reserved here",
            )
            .with_span_note(body.source_info(activation).span, "and used here")
            .emit();
    }
}

/// The places whose value decides which place `place` names: each prefix ending right before a
/// dereference, and each index local.
fn address_places<'tcx>(place: Place<'tcx>) -> Vec<PlaceRef<'tcx>> {
    let mut places = Vec::new();
    for (base, elem) in place.iter_projections() {
        match elem {
            PlaceElem::Deref => places.push(base),
            PlaceElem::Index(local) => places.push(PlaceRef {
                local,
                projection: &[],
            }),
            _ => {}
        }
    }
    places
}

/// Finds a write that may change one of `addresses`.
struct AddressWriteFinder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    addresses: Vec<PlaceRef<'tcx>>,
    /// A write that changes an address.
    write: Option<Location>,
    /// Writes that change an address unless two indices differ.
    obligations: Vec<(Location, Local, Local)>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for AddressWriteFinder<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if context.is_mutating_use() {
            for address in &self.addresses {
                match conflict(self.tcx, self.body, *place, *address) {
                    Conflict::Disjoint => {}
                    Conflict::Changes => self.write = Some(location),
                    Conflict::UnlessIndicesDiffer(reserved, written) => {
                        self.obligations.push((location, reserved, written));
                    }
                }
            }
        }
        self.super_place(place, context, location);
    }
}

/// How writing `written` affects the value at `address`.
enum Conflict {
    /// It does not change the address; a write through a dereference of `address` changes the
    /// pointee, not `address`.
    Disjoint,
    /// It may change the address.
    Changes,
    /// It changes the address when the two index locals are equal, and not otherwise: the
    /// places are the same up to indices, the first of the address, the second of the write.
    UnlessIndicesDiffer(Local, Local),
}

fn conflict<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    written: Place<'tcx>,
    address: PlaceRef<'tcx>,
) -> Conflict {
    if written.local != address.local {
        return Conflict::Disjoint;
    }
    let mut indices = None;
    let mut index_pairs = 0;
    let mut other_overlap = false;
    for (i, (base, elem)) in written.iter_projections().enumerate() {
        let Some(addressed) = address.projection.get(i) else {
            if elem == PlaceElem::Deref {
                return Conflict::Disjoint;
            }
            break;
        };
        if !elems_may_overlap(tcx, body, base, elem, *addressed) {
            return Conflict::Disjoint;
        }
        match (*addressed, elem) {
            (PlaceElem::Index(reserved), PlaceElem::Index(written)) if reserved != written => {
                indices = Some((reserved, written));
                index_pairs += 1;
            }
            _ => other_overlap |= *addressed != elem,
        }
    }
    match indices {
        Some((reserved, written)) if index_pairs == 1 && !other_overlap => {
            Conflict::UnlessIndicesDiffer(reserved, written)
        }
        _ => Conflict::Changes,
    }
}

/// Whether two projection elements of the same base may name overlapping parts, as rustc's
/// `place_projection_conflict` decides with `PlaceConflictBias::Overlap`: distinct fields of a
/// struct and distinct variants are disjoint, fields of a union and elements of a sequence may
/// overlap whatever the indices. Constant indices and subslices, which rustc tells apart by their
/// offsets, are taken to overlap.
fn elems_may_overlap<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    base: PlaceRef<'tcx>,
    a: PlaceElem<'tcx>,
    b: PlaceElem<'tcx>,
) -> bool {
    match (a, b) {
        (PlaceElem::Field(f, _), PlaceElem::Field(g, _)) => {
            f == g || base.ty(body, tcx).ty.is_union()
        }
        (PlaceElem::Downcast(_, v), PlaceElem::Downcast(_, w)) => v == w,
        _ => true,
    }
}

/// Moves each borrow right before its activation, or removes it when it is never used.
fn apply<'tcx>(body: &mut Body<'tcx>, moves: Vec<(TwoPhaseBorrow<'tcx>, Option<Location>)>) {
    let blocks = body.basic_blocks.as_mut_preserves_cfg();
    let mut inserts = Vec::new();
    for (borrow, activation) in moves {
        let from = borrow.reservation;
        let stmt = &mut blocks[from.block].statements[from.statement_index];
        let moved = stmt.clone();
        stmt.make_nop();
        if let Some(activation) = activation {
            inserts.push((activation, moved));
        }
    }
    // Inserting from the last location down keeps the earlier indices valid; the stable sort
    // keeps borrows created at one location in reservation order.
    inserts.sort_by_key(|(location, _)| (location.block, location.statement_index));
    for (location, stmt) in inserts.into_iter().rev() {
        blocks[location.block]
            .statements
            .insert(location.statement_index, stmt);
    }
}

/// The locations using `local`, its assignments included.
fn use_locations(body: &Body<'_>, local: Local) -> Vec<Location> {
    use mir::visit::Visitor as _;
    struct UseCollector {
        local: Local,
        uses: Vec<Location>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for UseCollector {
        fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
            if local == self.local && context.is_use() && !self.uses.contains(&location) {
                self.uses.push(location);
            }
        }
    }
    let mut collector = UseCollector {
        local,
        uses: Vec::new(),
    };
    collector.visit_body(body);
    collector.uses
}

fn fatal_at(tcx: TyCtxt<'_>, body: &Body<'_>, location: Location, msg: &'static str) -> ! {
    tcx.dcx().span_fatal(body.source_info(location).span, msg)
}

fn visit_location<'tcx>(
    body: &Body<'tcx>,
    visitor: &mut impl mir::visit::Visitor<'tcx>,
    location: Location,
) {
    let data = &body.basic_blocks[location.block];
    match data.statements.get(location.statement_index) {
        Some(stmt) => visitor.visit_statement(stmt, location),
        None => visitor.visit_terminator(data.terminator(), location),
    }
}

/// The statements and terminators on a path from `from` to `to`, both excluded. A path that
/// reaches `from` again starts over, so `from`'s block is not entered from its start.
fn locations_between(body: &Body<'_>, from: Location, to: Location) -> Vec<Location> {
    if from.block == to.block && from.statement_index < to.statement_index {
        return block_range(from.block, from.statement_index + 1, to.statement_index);
    }
    let stops = [from.block, to.block];
    let reached = reachable(from.block, &stops, |bb| {
        body.basic_blocks[bb].terminator().successors().collect()
    });
    let reaching = reachable(to.block, &stops, |bb| {
        body.basic_blocks.predecessors()[bb].to_vec()
    });
    let from_end = body.basic_blocks[from.block].statements.len();
    let mut locations = block_range(from.block, from.statement_index + 1, from_end + 1);
    for &bb in reached.intersection(&reaching) {
        if stops.contains(&bb) {
            continue;
        }
        let end = body.basic_blocks[bb].statements.len();
        locations.extend(block_range(bb, 0, end + 1));
    }
    locations.extend(block_range(to.block, 0, to.statement_index));
    locations
}

fn block_range(block: BasicBlock, start: usize, end: usize) -> Vec<Location> {
    (start..end)
        .map(|statement_index| Location {
            block,
            statement_index,
        })
        .collect()
}

/// The blocks reached from `start` by `next`, not continuing past a block of `stops`.
fn reachable(
    start: BasicBlock,
    stops: &[BasicBlock],
    next: impl Fn(BasicBlock) -> Vec<BasicBlock>,
) -> HashSet<BasicBlock> {
    let mut reached = HashSet::new();
    let mut stack = next(start);
    while let Some(bb) = stack.pop() {
        if !reached.insert(bb) || stops.contains(&bb) {
            continue;
        }
        stack.extend(next(bb));
    }
    reached
}
