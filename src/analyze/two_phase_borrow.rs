//! Creates each two-phase mutable borrow at its activation, as Creusot does.
//!
//! A two-phase borrow `_t = &mut place` (an autoref'd receiver) only reserves `place` until `_t`
//! is used, and code in between may read `place`, as in `c.set(c.get() + 1)`. Thrust replaces
//! a borrowed place by the borrow's prophecy where the borrow is created, so the borrow is moved
//! right before the activation, the unique use of `_t`, when the code in between reads the
//! lender (the local `place` starts from). `InstSimplify` turns a reborrow `&mut *p` into
//! `copy p`, which Thrust reborrows as well; such a copy into a local used once is moved the same
//! way. When a pointer `place` goes through is overwritten before the activation
//! (`p.0.set({ p = &mut b; 5 })`), the borrow is created before the first such write instead.

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

fn reservations<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Vec<Reservation<'tcx>> {
    let mut reservations = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let Some((lhs, rvalue)) = stmt.kind.as_assign() else {
                continue;
            };
            let (place, copied) = match rvalue {
                mir::Rvalue::Ref(_, kind, place) if kind.allows_two_phase_borrow() => {
                    (*place, false)
                }
                mir::Rvalue::Use(mir::Operand::Copy(p)) if is_mut_ref(tcx, body, p) => {
                    (tcx.mk_place_deref(*p), true)
                }
                _ => continue,
            };
            let Some(temp) = lhs.as_local() else {
                assert!(copied, "two-phase borrow must assign to a local");
                continue;
            };
            let location = Location {
                block,
                statement_index,
            };
            reservations.push(Reservation {
                location,
                temp,
                place,
                copied,
            });
        }
    }
    reservations
}

fn is_mut_ref<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: &Place<'tcx>) -> bool {
    matches!(
        place.ty(body, tcx).ty.kind(),
        mir_ty::TyKind::Ref(_, _, mir_ty::Mutability::Mut)
    )
}

fn plan<'tcx>(body: &Body<'tcx>, reservations: Vec<Reservation<'tcx>>) -> Vec<Move> {
    let uses = temp_uses(body, &reservations);
    let mut moves = Vec::new();
    for reservation in reservations {
        let uses = &uses[&reservation.temp];
        if reservation.copied && uses.len() != 1 {
            continue;
        }
        let Some(activation) = activation(body, &reservation, uses) else {
            moves.push(Move {
                from: reservation.location,
                to: None,
            });
            continue;
        };
        let between = Between::visit(body, &reservation, activation);
        if !between.reads_lender {
            continue;
        }
        let to = creation_point(body, &between.address_writes, activation).unwrap_or_else(|| {
            unimplemented!(
                "two-phase borrow of {:?}: the pointers it goes through are overwritten on several paths",
                reservation.place
            )
        });
        assert!(
            !reads_at(body, reservation.place.local, to),
            "two-phase borrow of {:?}: its lender is read where it is created",
            reservation.place
        );
        moves.push(Move {
            from: reservation.location,
            to: Some(to),
        });
    }
    moves
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

/// The locations using each reservation's temporary, the reservation excluded.
fn temp_uses(body: &Body<'_>, reservations: &[Reservation<'_>]) -> HashMap<Local, Vec<Location>> {
    use mir::visit::Visitor as _;
    struct UseCollector<'a> {
        reservations: HashMap<Local, Vec<Location>>,
        uses: &'a mut HashMap<Local, Vec<Location>>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for UseCollector<'_> {
        fn visit_local(&mut self, local: Local, context: PlaceContext, location: Location) {
            let Some(reserved_at) = self.reservations.get(&local) else {
                return;
            };
            if !context.is_use() || reserved_at.contains(&location) {
                return;
            }
            let uses = self.uses.entry(local).or_default();
            if !uses.contains(&location) {
                uses.push(location);
            }
        }
    }
    let mut reserved_at: HashMap<Local, Vec<Location>> = HashMap::new();
    for reservation in reservations {
        reserved_at
            .entry(reservation.temp)
            .or_default()
            .push(reservation.location);
    }
    let mut uses: HashMap<Local, Vec<Location>> =
        reserved_at.keys().map(|&temp| (temp, Vec::new())).collect();
    // A temporary assigned by two copies counts the other copy as a use.
    for (&temp, locations) in &reserved_at {
        if locations.len() > 1 {
            uses.get_mut(&temp).unwrap().extend(locations);
        }
    }
    UseCollector {
        reservations: reserved_at,
        uses: &mut uses,
    }
    .visit_body(body);
    uses
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

/// Where the moved borrow is created: before the first overwrite of a pointer the borrowed place
/// goes through, so that the place still names the reserved one, or at the activation when there
/// is none. The first overwrite must come before the others and the activation.
fn creation_point(
    body: &Body<'_>,
    address_writes: &[Location],
    activation: Location,
) -> Option<Location> {
    if address_writes.is_empty() {
        return Some(activation);
    }
    let dominators = body.basic_blocks.dominators();
    let dominates_rest = |first: &Location| {
        address_writes
            .iter()
            .chain([&activation])
            .all(|other| first.dominates(*other, dominators))
    };
    address_writes.iter().copied().find(dominates_rest)
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
struct Between<'tcx> {
    lender: Local,
    address_places: Vec<PlaceRef<'tcx>>,
    reads_lender: bool,
    address_writes: Vec<Location>,
}

impl<'tcx> Between<'tcx> {
    fn visit(body: &Body<'tcx>, reservation: &Reservation<'tcx>, activation: Location) -> Self {
        let mut between = Between {
            lender: reservation.place.local,
            address_places: address_places(reservation.place),
            reads_lender: false,
            address_writes: Vec::new(),
        };
        for location in locations_between(body, reservation.location, activation) {
            visit_location(body, &mut between, location);
        }
        between
    }
}

impl<'tcx> mir::visit::Visitor<'tcx> for Between<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let is_prefix = |address: &PlaceRef<'tcx>| {
            place.local == address.local && address.projection.starts_with(place.projection)
        };
        if context.is_mutating_use() && self.address_places.iter().any(is_prefix) {
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

/// Whether the statement or terminator at `location` reads `lender`.
fn reads_at(body: &Body<'_>, lender: Local, location: Location) -> bool {
    struct Reader {
        lender: Local,
        reads: bool,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Reader {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _location: Location) {
            if local == self.lender && matches!(context, PlaceContext::NonMutatingUse(_)) {
                self.reads = true;
            }
        }
    }
    let mut reader = Reader {
        lender,
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
