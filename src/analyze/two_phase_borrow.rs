//! Creates each two-phase mutable borrow at its activation, as Creusot does, and refuses one
//! whose reserved place may change before it.
//!
//! A two-phase borrow `_t = &mut place` (an autoref'd receiver) only reserves `place` until `_t`
//! is used, and code in between may read `place`, as in `c.set(c.get() + 1)`. Thrust replaces
//! a borrowed place by the borrow's prophecy where the borrow is created, so the borrow is moved
//! right before the activation, the unique use of `_t`, when the code in between reads the
//! lender (the local `place` starts from). `InstSimplify` turns a reborrow `&mut *p` into
//! `copy p`, which Thrust reborrows as well; such a copy into a local used once is moved the same
//! way. The borrow of a slice element (`s[0].bump(s[1])`) is created at the same point by the
//! reconstruction of its `IndexMut::index_mut` call.
//!
//! Soundness: rustc evaluates `place` once, at the reservation, and until the activation allows
//! only reads of it and writes that do not overlap it. [`reject_reserved_place_changes`] refuses
//! a write in between that may overlap a pointer `place` goes through (a prefix ending before a
//! `Deref`, also through the copies of `&mut` that compute it) or an index local of `place`.
//! Without one, `place` names the same memory at both points, so the borrow created at the
//! activation is the one rustc makes and the reads in between see the current value; a borrow
//! left at its reservation, with no read of the lender in between, is the same borrow.
//!
//! - rustc: two-phase borrows in the rustc dev guide; the overlap is `place_projection_conflict`
//!   with `PlaceConflictBias::Overlap` (elements of one sequence may overlap).
//! - Creusot creates the borrow at the activation too: `activate_two_phases` in
//!   `creusot/src/analysis.rs`, applied in `translation/function/statement.rs`.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{
    self, visit::PlaceContext, BasicBlock, Body, Local, Location, Place, PlaceElem, PlaceRef,
};
use rustc_middle::ty::{self as mir_ty, TyCtxt};

struct Reservation<'tcx> {
    location: Location,
    temp: Local,
    place: Place<'tcx>,
    /// A reborrow that `InstSimplify` turned into `copy p`: it may not be two-phase at all, and
    /// it is moved only when its temporary has one use.
    copied: bool,
}

/// The borrow statement at `from` moves before `to`, or is removed when there is no `to`.
struct Move {
    from: Location,
    to: Option<Location>,
}

pub fn move_to_activation<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
    let moves = plan(body, reservations(tcx, body));
    apply(body, moves);
}

/// Stops with an error at a write between a two-phase borrow's reservation and its activation
/// that may change which place the borrow names: a write that may overlap a pointer the borrowed
/// place goes through, or one of its index locals. Runs before the slice indexing the borrowed
/// place goes through is reconstructed into calls, while its writes still name the place.
pub fn reject_reserved_place_changes<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
    let reservations = reservations(tcx, body);
    let temp_uses = temp_uses(body, &reservations);
    let activations: Vec<_> = reservations
        .iter()
        .map(|reservation| two_phase_activation(body, reservation, &temp_uses))
        .collect();
    for (reservation, activation) in reservations.iter().zip(&activations) {
        let Some(activation) = *activation else {
            continue;
        };
        let (from, place) = reserved_through_copies(tcx, &reservations, &activations, reservation);
        let between = Between::visit(body, from, place, activation);
        if let Some(&write) = between.address_writes.first() {
            tcx.dcx().span_fatal(
                body.source_info(write).span,
                "thrust: this may change which place a two-phase borrow names before the borrow \
                 is used, which is not supported",
            );
        }
    }
}

/// Where the reservation starts and the place it reserves, through the copies of `&mut`
/// references activated by it: of `_18 = copy (*_17)` after `_17 = copy (*s)[i]`, which compute
/// the receiver of `(**s[i]).bump(..)`, the place `**(*s)[i]` reserved from the first copy on.
fn reserved_through_copies<'tcx>(
    tcx: TyCtxt<'tcx>,
    reservations: &[Reservation<'tcx>],
    activations: &[Option<Location>],
    reservation: &Reservation<'tcx>,
) -> (Location, Place<'tcx>) {
    let mut from = reservation.location;
    let mut place = reservation.place;
    loop {
        let Some((copy, _)) = reservations
            .iter()
            .zip(activations)
            .find(|(copy, activation)| {
                copy.copied && copy.temp == place.local && **activation == Some(from)
            })
        else {
            break;
        };
        // A copy `_u = copy q` reserves `*q`; `place` goes through `*_u`, which is `*q`.
        let (_, q) = copy.place.projection.split_last().unwrap();
        let q = Place {
            local: copy.place.local,
            projection: tcx.mk_place_elems(q),
        };
        place = q.project_deeper(place.projection, tcx);
        from = copy.location;
    }
    (from, place)
}

fn reservations<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<Reservation<'tcx>> {
    let mut reservations = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for statement_index in 0..data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            reservations.extend(reservation_at(tcx, body, location));
        }
    }
    reservations
}

/// The reservation the statement at `location` makes, if it is one.
fn reservation_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    location: Location,
) -> Option<Reservation<'tcx>> {
    let stmt = body.basic_blocks[location.block]
        .statements
        .get(location.statement_index)?;
    let (lhs, rvalue) = stmt.kind.as_assign()?;
    let (place, copied) = match rvalue {
        mir::Rvalue::Ref(_, kind, place) if kind.allows_two_phase_borrow() => (*place, false),
        mir::Rvalue::Use(mir::Operand::Copy(p)) if is_mut_ref(tcx, body, p) => {
            (tcx.mk_place_deref(*p), true)
        }
        _ => return None,
    };
    let Some(temp) = lhs.as_local() else {
        assert!(copied, "two-phase borrow must assign to a local");
        return None;
    };
    Some(Reservation {
        location,
        temp,
        place,
        copied,
    })
}

fn is_mut_ref<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: &Place<'tcx>) -> bool {
    matches!(
        place.ty(body, tcx).ty.kind(),
        mir_ty::TyKind::Ref(_, _, mir_ty::Mutability::Mut)
    )
}

/// Where [`move_to_activation`] creates the two-phase borrow `_t = &mut place` or reborrow
/// `_t = copy p` at `location`, its activation, when it moves the borrow there.
pub fn moved_creation_point<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    location: Location,
) -> Option<Location> {
    let reservation = reservation_at(tcx, body, location)?;
    let temp_uses = temp_uses(body, std::slice::from_ref(&reservation));
    planned_move(body, &reservation, &temp_uses)?.to
}

fn plan<'tcx>(body: &Body<'tcx>, reservations: Vec<Reservation<'tcx>>) -> Vec<Move> {
    let temp_uses = temp_uses(body, &reservations);
    reservations
        .iter()
        .filter_map(|reservation| planned_move(body, reservation, &temp_uses))
        .collect()
}

/// The move of the reservation's borrow, or `None` when it stays where it is.
fn planned_move<'tcx>(
    body: &Body<'tcx>,
    reservation: &Reservation<'tcx>,
    temp_uses: &HashMap<Local, Vec<Location>>,
) -> Option<Move> {
    let Some(activation) = two_phase_activation(body, reservation, temp_uses) else {
        return (!reservation.copied).then_some(Move {
            from: reservation.location,
            to: None,
        });
    };
    let between = Between::visit(body, reservation.location, reservation.place, activation);
    if !between.reads_lender {
        return None;
    }
    assert!(
        !repeats_without(body, reservation.location, activation),
        "two-phase borrow of {:?}: it would be created again in a loop",
        reservation.place
    );
    assert!(
        !reads_overlapping_at(body, reservation.place, activation),
        "two-phase borrow of {:?}: the borrowed place is read where the borrow is created",
        reservation.place
    );
    Some(Move {
        from: reservation.location,
        to: Some(activation),
    })
}

/// The activation of the reservation's borrow, or `None` when its temporary is never used or,
/// for a copy, when the copy may not be a two-phase borrow: its temporary has several uses, or
/// the use may run again without the copy.
fn two_phase_activation<'tcx>(
    body: &Body<'tcx>,
    reservation: &Reservation<'tcx>,
    temp_uses: &HashMap<Local, Vec<Location>>,
) -> Option<Location> {
    let uses: Vec<Location> = temp_uses[&reservation.temp]
        .iter()
        .copied()
        .filter(|location| *location != reservation.location)
        .collect();
    if reservation.copied && uses.len() != 1 {
        return None;
    }
    let activation = activation(body, reservation, &uses)?;
    if reservation.copied && repeats_without(body, reservation.location, activation) {
        return None;
    }
    Some(activation)
}

/// Whether `to` can run again after itself without `from` running in between, as in a loop
/// that `from` is outside of.
fn repeats_without(body: &Body<'_>, from: Location, to: Location) -> bool {
    if from.block == to.block {
        return false;
    }
    let successors = |bb: BasicBlock| body.basic_blocks[bb].terminator().successors().collect();
    reachable(to.block, &[from.block, to.block], successors).contains(&to.block)
}

fn apply(body: &mut Body<'_>, moves: Vec<Move>) {
    let blocks = body.basic_blocks.as_mut_preserves_cfg();
    let mut inserts = Vec::new();
    for Move { from, to } in moves {
        let stmt = &mut blocks[from.block].statements[from.statement_index];
        let moved = stmt.clone();
        stmt.make_nop();
        if let Some(to) = to {
            inserts.push((to, moved));
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

/// The locations using each reservation's temporary, its assignments included.
fn temp_uses(body: &Body<'_>, reservations: &[Reservation<'_>]) -> HashMap<Local, Vec<Location>> {
    use mir::visit::Visitor as _;
    struct UseCollector {
        uses: HashMap<Local, Vec<Location>>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for UseCollector {
        fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
            let Some(uses) = self.uses.get_mut(&local) else {
                return;
            };
            if context.is_use() && !uses.contains(&location) {
                uses.push(location);
            }
        }
    }
    let uses = reservations
        .iter()
        .map(|reservation| (reservation.temp, Vec::new()))
        .collect();
    let mut collector = UseCollector { uses };
    collector.visit_body(body);
    collector.uses
}

/// The use of a two-phase borrow's temporary that dominates its other uses; rustc's `BorrowSet`
/// finds the only one before optimization.
fn activation(
    body: &Body<'_>,
    reservation: &Reservation<'_>,
    uses: &[Location],
) -> Option<Location> {
    let dominators = body.basic_blocks.dominators();
    let first = uses
        .iter()
        .copied()
        .find(|first| uses.iter().all(|other| first.dominates(*other, dominators)));
    assert!(
        uses.is_empty() || first.is_some(),
        "two-phase borrow temporary {:?} used on several paths: {:?}",
        reservation.temp,
        uses
    );
    first
}

/// The places whose value decides which place `place` names: each pointer it dereferences and
/// each index local.
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

/// Whether two projection elements may name the same part of a place. Elements of one sequence
/// (an index, a constant index, a subslice) may overlap whatever the index values, as in rustc's
/// `places_conflict` with `PlaceConflictBias::Overlap`; every other element names a fixed part.
fn elems_may_overlap<'tcx>(a: PlaceElem<'tcx>, b: PlaceElem<'tcx>) -> bool {
    let is_sequence_element = |elem: &PlaceElem<'tcx>| {
        matches!(
            elem,
            PlaceElem::Index(_) | PlaceElem::ConstantIndex { .. } | PlaceElem::Subslice { .. }
        )
    };
    if is_sequence_element(&a) && is_sequence_element(&b) {
        return true;
    }
    a == b
}

/// What the code on a path from a reservation to its activation does with the borrowed place.
struct Between<'tcx> {
    lender: Local,
    address_places: Vec<PlaceRef<'tcx>>,
    reads_lender: bool,
    address_writes: Vec<Location>,
}

impl<'tcx> Between<'tcx> {
    /// What the code from `reservation`, which reserves `place`, to `activation` does.
    fn visit(
        body: &Body<'tcx>,
        reservation: Location,
        place: Place<'tcx>,
        activation: Location,
    ) -> Self {
        let mut between = Between {
            lender: place.local,
            address_places: address_places(place),
            reads_lender: false,
            address_writes: Vec::new(),
        };
        for location in locations_between(body, reservation, activation) {
            visit_location(body, &mut between, location);
        }
        between
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for Between<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let may_name_address = |address: &PlaceRef<'tcx>| {
            place.local == address.local
                && place.projection.len() <= address.projection.len()
                && place
                    .projection
                    .iter()
                    .zip(address.projection)
                    .all(|(written, addressed)| elems_may_overlap(written, *addressed))
        };
        if context.is_mutating_use() && self.address_places.iter().any(may_name_address) {
            self.address_writes.push(location);
        }
        self.super_place(place, context, location);
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
        if local == self.lender && matches!(context, PlaceContext::NonMutatingUse(_)) {
            self.reads_lender = true;
        }
    }
}

/// Whether the statement or terminator at `location` reads a place overlapping `borrowed`.
fn reads_overlapping_at<'tcx>(
    body: &Body<'tcx>,
    borrowed: Place<'tcx>,
    location: Location,
) -> bool {
    struct Reader<'tcx> {
        borrowed: Place<'tcx>,
        reads: bool,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Reader<'tcx> {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
            let overlaps = place.local == self.borrowed.local
                && (place.projection.starts_with(self.borrowed.projection)
                    || self.borrowed.projection.starts_with(place.projection));
            if overlaps && matches!(context, PlaceContext::NonMutatingUse(_)) {
                self.reads = true;
            }
        }
    }
    let mut reader = Reader {
        borrowed,
        reads: false,
    };
    visit_location(body, &mut reader, location);
    reader.reads
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
