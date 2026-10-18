//! Moves each two-phase mutable borrow to its activation.
//!
//! A two-phase borrow `_t = &mut place` (an autoref'd method receiver, an overloaded compound
//! assignment) only reserves `place`: until `_t` is first used, `place` may still be read, as
//! in `c.set(c.get() + 1)`. Thrust replaces a borrowed place by the borrow's prophecy when the
//! borrow is created, so a read in between would see the prophecy instead of the value. Creating
//! the borrow at the activation, as Creusot does, gives those reads the value at the reservation:
//! the borrow checker allows no write to `place` before the activation.
//!
//! The activation is the unique use of `_t` after the reservation, found as rustc's `BorrowSet`
//! finds it. When the code between the two reads the local `place` starts from, the reservation
//! is moved right before the activation, into the same block; otherwise the move would change
//! nothing and the borrow stays. A borrow that is never activated is removed. The borrow checker
//! does allow a write to a pointer that `place` goes through, as in
//! `p.0.set({ p = &mut b; p.0.get() })`, which would make the moved borrow name another place;
//! such a borrow is not supported.

use std::collections::HashSet;

use rustc_middle::mir::{
    self, visit::PlaceContext, BasicBlock, Body, Local, Location, Place, PlaceElem, PlaceRef,
};

struct Reservation<'tcx> {
    location: Location,
    temp: Local,
    place: Place<'tcx>,
}

struct UseCollector<'tcx> {
    reservations: Vec<Reservation<'tcx>>,
    uses: Vec<Vec<Location>>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for UseCollector<'tcx> {
    fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
        if !context.is_use() {
            return;
        }
        for (reservation, uses) in self.reservations.iter().zip(self.uses.iter_mut()) {
            if reservation.temp == local && reservation.location != location {
                uses.push(location);
            }
        }
    }
}

fn reservations<'tcx>(body: &Body<'tcx>) -> Vec<Reservation<'tcx>> {
    let mut reservations = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let Some((lhs, mir::Rvalue::Ref(_, kind, place))) = stmt.kind.as_assign() else {
                continue;
            };
            if !kind.allows_two_phase_borrow() {
                continue;
            }
            let temp = lhs
                .as_local()
                .expect("two-phase borrow must assign to a local");
            let location = Location {
                block,
                statement_index,
            };
            reservations.push(Reservation {
                location,
                temp,
                place: *place,
            });
        }
    }
    reservations
}

/// The activation of each reservation, `None` when the borrow is never used.
fn activations<'tcx>(
    body: &Body<'tcx>,
    reservations: Vec<Reservation<'tcx>>,
) -> Vec<(Reservation<'tcx>, Option<Location>)> {
    use mir::visit::Visitor as _;
    let uses = reservations.iter().map(|_| Vec::new()).collect();
    let mut collector = UseCollector { reservations, uses };
    collector.visit_body(body);
    collector
        .reservations
        .into_iter()
        .zip(collector.uses)
        .map(|(reservation, uses)| {
            assert!(
                uses.len() <= 1,
                "two-phase borrow temporary {:?} used more than once: {:?}",
                reservation.temp,
                uses
            );
            let activation = uses.first().copied();
            (reservation, activation)
        })
        .collect()
}

pub fn move_to_activation(body: &mut Body<'_>) {
    let mut moves = Vec::new();
    for (reservation, activation) in activations(body, reservations(body)) {
        let Some(activation) = activation else {
            moves.push((reservation.location, None));
            continue;
        };
        let between = Between::visit(body, &reservation, activation);
        if !between.reads_lender {
            continue;
        }
        assert!(
            !between.writes_address,
            "two-phase borrow of {:?}: a pointer it goes through is written before its activation",
            reservation.place
        );
        moves.push((reservation.location, Some(activation)));
    }
    let blocks = body.basic_blocks.as_mut_preserves_cfg();
    let mut inserts = Vec::new();
    for (reservation, activation) in moves {
        let stmt = &mut blocks[reservation.block].statements[reservation.statement_index];
        let moved = stmt.clone();
        stmt.make_nop();
        if let Some(activation) = activation {
            inserts.push((activation, moved));
        }
    }
    // Inserting from the last location down keeps the earlier indices valid; the stable sort
    // keeps borrows activated at one location in reservation order.
    inserts.sort_by_key(|(location, _)| (location.block, location.statement_index));
    for (location, stmt) in inserts.into_iter().rev() {
        blocks[location.block]
            .statements
            .insert(location.statement_index, stmt);
    }
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

/// What the code on a path from a reservation to its activation does with the borrowed place.
/// Moving the borrow matters only when that code reads the lender, the local the place starts
/// from.
struct Between<'tcx> {
    lender: Local,
    address_places: Vec<PlaceRef<'tcx>>,
    reads_lender: bool,
    writes_address: bool,
}

impl<'tcx> Between<'tcx> {
    fn visit(body: &Body<'tcx>, reservation: &Reservation<'tcx>, activation: Location) -> Self {
        use mir::visit::Visitor as _;
        let mut between = Between {
            lender: reservation.place.local,
            address_places: address_places(reservation.place),
            reads_lender: false,
            writes_address: false,
        };
        for location in locations_between(body, reservation.location, activation) {
            let data = &body.basic_blocks[location.block];
            match data.statements.get(location.statement_index) {
                Some(stmt) => between.visit_statement(stmt, location),
                None => between.visit_terminator(data.terminator(), location),
            }
        }
        between
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for Between<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if matches!(context, PlaceContext::NonMutatingUse(_)) && place.local == self.lender {
            self.reads_lender = true;
        }
        let is_prefix = |address: &PlaceRef<'tcx>| {
            place.local == address.local && address.projection.starts_with(place.projection)
        };
        if context.is_mutating_use() && self.address_places.iter().any(is_prefix) {
            self.writes_address = true;
        }
        self.super_place(place, context, location);
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
