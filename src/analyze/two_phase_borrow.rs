//! Reads of a place a two-phase mutable borrow has reserved.
//!
//! A two-phase borrow `_t = &mut P` (an autoref'd receiver, `x.bump(arg)`) only reserves `P`
//! until its activation, the unique use of `_t`; the code in between, the window, may read `P`.
//! rustc evaluates `P` once, at the reservation, and until the activation the memory it names
//! holds the value it held there: every write, move or mutable borrow of an overlapping place is
//! rejected, and a write to a pointer `P` goes through only cuts the path.
//!
//! Thrust borrows at the reservation exactly as for any mutable borrow, so the lender holds the
//! borrow's prophecy from there on, and a read of `P` in the window has to see the borrow's
//! current value instead. [`redirect_window_reads`] rewrites each such read to a read through
//! `_t` (`P.f` becomes `(*_t).f`), and [`WindowReads`] does the same for a variable a formula
//! names. A read of a place that is disjoint from `P`, or that goes through a pointer a write in
//! the window has re-pointed, is left as it is. A read Thrust cannot place is refused:
//!
//! - a window that holds a read of `P` through a raw pointer or of a type with interior mutability;
//! - a read of an ancestor of `P` for its value (`p` for `P = *p`);
//! - a read of `P` after a write that may re-point a pointer `P` goes through (a write through an
//!   index that may or may not be the reserved one);
//! - a read of a place that differs from `P` in an index the analysis cannot compare (two indices
//!   that are not the same constant);
//! - a borrow that is not used exactly once after it is made, or that its reservation does not
//!   dominate.
//!
//! Thrust reads MIR without `InstSimplify`, which would turn a reborrow `&mut *p` into `copy p`
//! and lose its two-phase kind. Whether a read or a write in the window overlaps the reserved
//! place is rustc's `places_conflict`, a relation of places that does not depend on the borrow
//! checker (NLL or Polonius).

use std::collections::HashSet;

use rustc_borrowck::consumers::{places_conflict, PlaceConflictBias};

use rustc_middle::mir::{
    self,
    visit::{MutVisitor, NonMutatingUseContext, PlaceContext},
    BasicBlock, Body, Local, Location, Place, PlaceElem,
};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_span::Span;

/// A two-phase borrow `temp = &mut place` made at `reservation`.
struct TwoPhaseBorrow<'tcx> {
    reservation: Location,
    temp: Local,
    place: Place<'tcx>,
}

/// What the pointers `P` goes through hold at a location of the window.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Pointers {
    /// No write since the reservation re-pointed one: `P` names the reserved memory.
    Intact,
    /// A write on every path since the reservation re-pointed one: `P` names other memory.
    Repointed,
    /// Some path re-pointed one, or the analysis cannot tell.
    Unknown,
}

/// How a write in the window affects the pointers the reserved place goes through.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Repoint {
    Always,
    Maybe,
}

/// A reserved place with its window: what is needed to say how a read in it is read.
#[derive(Clone)]
struct Window<'tcx> {
    temp: Local,
    place: Place<'tcx>,
    blocks: HashSet<BasicBlock>,
    repoints: Vec<(Location, Repoint)>,
}

/// How a read of a place relates to the reserved place.
enum Overlap {
    Disjoint,
    /// Whether the places overlap depends on indices the analysis cannot compare.
    Undecided,
    /// The read place is the reserved place, a part of it, or an ancestor of it.
    Within(Relation),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Relation {
    /// The reserved place itself or a place inside it.
    Inside,
    /// A place the reserved place is inside of: its value includes the reserved memory.
    Ancestor,
}

/// How a read of a place in the window is carried out.
enum Reading<'tcx> {
    /// As written.
    Native,
    /// Through the borrow, which holds the reserved value.
    Through(Place<'tcx>),
    /// Not supported, with the reason.
    Refused(&'static str),
}

impl<'tcx> Window<'tcx> {
    /// How the read of `read` at a location where the pointers are `pointers` is carried out.
    /// `shape_only` is set for a read of the discriminant or the length of `read`.
    fn reading(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        read: Place<'tcx>,
        shape_only: bool,
        pointers: Pointers,
    ) -> Reading<'tcx> {
        let relation = match overlap(tcx, body, read, self.place) {
            Overlap::Disjoint => return Reading::Native,
            Overlap::Undecided if pointers == Pointers::Repointed => return Reading::Native,
            Overlap::Undecided => {
                return Reading::Refused(
                    "this read may or may not be of the place a two-phase mutable borrow has \
                     reserved, depending on indices Thrust cannot compare",
                )
            }
            Overlap::Within(relation) => relation,
        };
        if pointers == Pointers::Repointed {
            return Reading::Native;
        }
        // The shape of an ancestor (its length, its variant) does not include the reserved part.
        if shape_only && relation == Relation::Ancestor {
            return Reading::Native;
        }
        if pointers == Pointers::Unknown {
            return Reading::Refused(
                "this read follows a write that may re-point a pointer the place of a two-phase \
                 mutable borrow goes through; Thrust cannot tell whether it reads the reserved place",
            );
        }
        match relation {
            Relation::Ancestor => Reading::Refused(
                "this reads the value of a place that holds the place of a two-phase mutable \
                 borrow; Thrust supports only reads of the reserved place itself and of parts of it",
            ),
            Relation::Inside => Reading::Through(self.through_borrow(tcx, read)),
        }
    }

    /// The place `read` names inside the reserved place, as a place of the borrow.
    fn through_borrow(&self, tcx: TyCtxt<'tcx>, read: Place<'tcx>) -> Place<'tcx> {
        let inside = &read.projection.as_slice()[self.place.projection.len()..];
        Place {
            local: self.temp,
            projection: tcx.mk_place_elems_from_iter(
                std::iter::once(PlaceElem::Deref).chain(inside.iter().copied()),
            ),
        }
    }

    /// The pointers the reserved place goes through at `location`.
    fn pointers_at(&self, body: &Body<'tcx>, location: Location) -> Pointers {
        let dominators = body.basic_blocks.dominators();
        let before: Vec<(Location, Repoint)> = self
            .repoints
            .iter()
            .copied()
            .filter(|(write, _)| self.reaches(body, *write, location))
            .collect();
        if before.is_empty() {
            return Pointers::Intact;
        }
        let certain = before.iter().all(|(_, kind)| *kind == Repoint::Always);
        let on_every_path = before
            .iter()
            .any(|(write, _)| write.dominates(location, dominators));
        if certain && on_every_path {
            Pointers::Repointed
        } else {
            Pointers::Unknown
        }
    }

    /// Whether `to` may be reached after `from` without leaving the window.
    fn reaches(&self, body: &Body<'tcx>, from: Location, to: Location) -> bool {
        if from.block == to.block && from.statement_index < to.statement_index {
            return true;
        }
        let mut seen = HashSet::new();
        let mut stack: Vec<BasicBlock> = successors_in(body, from.block, &self.blocks);
        while let Some(block) = stack.pop() {
            if block == to.block {
                return true;
            }
            if seen.insert(block) {
                stack.extend(successors_in(body, block, &self.blocks));
            }
        }
        false
    }
}

fn successors_in(
    body: &Body<'_>,
    block: BasicBlock,
    blocks: &HashSet<BasicBlock>,
) -> Vec<BasicBlock> {
    let successors = body.basic_blocks[block].terminator().successors();
    successors.filter(|next| blocks.contains(next)).collect()
}

/// Whether and how `read` overlaps `reserved`. rustc's `places_conflict` rules out disjoint
/// places (other locals, fields, variants, constant indices); of the rest, a read is of the
/// reserved place, a part or an ancestor of it only when the two agree on their common prefix
/// ([`same_prefix`]).
fn overlap<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    read: Place<'tcx>,
    reserved: Place<'tcx>,
) -> Overlap {
    if !places_conflict(tcx, body, reserved, read, PlaceConflictBias::Overlap) {
        return Overlap::Disjoint;
    }
    match same_prefix(body, read, reserved) {
        Some(true) if read.projection.len() >= reserved.projection.len() => {
            Overlap::Within(Relation::Inside)
        }
        Some(true) => Overlap::Within(Relation::Ancestor),
        Some(false) => Overlap::Disjoint,
        None => Overlap::Undecided,
    }
}

/// Whether `a` and `b` name the same place up to the shorter of the two: `Some(false)` when an
/// index pair is two different constants, `None` when an index pair cannot be compared or two
/// other projections differ (fields of a union, overlapping subslices).
fn same_prefix<'tcx>(body: &Body<'tcx>, a: Place<'tcx>, b: Place<'tcx>) -> Option<bool> {
    let mut decided = Some(true);
    for (x, y) in a.projection.iter().zip(b.projection.iter()) {
        if x == y {
            continue;
        }
        let (PlaceElem::Index(x), PlaceElem::Index(y)) = (x, y) else {
            decided = None;
            continue;
        };
        match same_index(body, x, y) {
            Some(false) => return Some(false),
            Some(true) => {}
            None => decided = None,
        }
    }
    decided
}

/// Whether two index locals hold the same value, when both are assigned one constant.
fn same_index(body: &Body<'_>, a: Local, b: Local) -> Option<bool> {
    let (a, b) = (assigned_constant(body, a)?, assigned_constant(body, b)?);
    if a == b {
        return Some(true);
    }
    // Different constants are different values only once they are evaluated.
    Some(false).filter(|_| a.try_to_scalar_int().is_some() && b.try_to_scalar_int().is_some())
}

/// The constant `local` is assigned, when that is its only assignment.
fn assigned_constant<'tcx>(body: &Body<'tcx>, local: Local) -> Option<mir::Const<'tcx>> {
    use mir::visit::Visitor as _;
    struct ConstantAssignments<'tcx> {
        local: Local,
        assignments: usize,
        constants: Vec<mir::Const<'tcx>>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for ConstantAssignments<'tcx> {
        fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
            if local == self.local && context.is_mutating_use() {
                self.assignments += 1;
            }
        }
        fn visit_assign(
            &mut self,
            place: &Place<'tcx>,
            rvalue: &mir::Rvalue<'tcx>,
            location: Location,
        ) {
            if place.as_local() == Some(self.local) {
                if let mir::Rvalue::Use(mir::Operand::Constant(constant)) = rvalue {
                    self.constants.push(constant.const_);
                }
            }
            self.super_assign(place, rvalue, location);
        }
    }
    let mut finder = ConstantAssignments {
        local,
        assignments: 0,
        constants: Vec::new(),
    };
    finder.visit_body(body);
    match (finder.assignments, finder.constants.as_slice()) {
        (1, [constant]) => Some(*constant),
        _ => None,
    }
}

/// The reads in the windows of two-phase borrows that formulas make: the variables they name.
/// Keyed by the span of the terminator that holds the formula.
#[derive(Clone, Default)]
pub struct WindowReads<'tcx> {
    formulas: Vec<(Span, Window<'tcx>, Pointers)>,
}

impl<'tcx> WindowReads<'tcx> {
    /// The place a formula at the terminator spanning `span` reads for the variable at `place`.
    pub fn read_by_formula(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        span: Span,
        place: Place<'tcx>,
    ) -> Place<'tcx> {
        let mut read = place;
        for (_, window, pointers) in self.formulas.iter().filter(|(at, ..)| *at == span) {
            match window.reading(tcx, body, read, false, *pointers) {
                Reading::Native => {}
                Reading::Through(through) => {
                    refuse_unsupported_path(tcx, body, window.place, span);
                    read = through;
                }
                Reading::Refused(reason) => tcx.dcx().span_fatal(span, reason),
            }
        }
        read
    }
}

/// Redirects the reads in the window of each two-phase borrow to the borrow ([`Window::reading`]).
/// Returns the windows' terminators, which formulas read variables at.
pub fn redirect_window_reads<'tcx>(tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) -> WindowReads<'tcx> {
    let mut formulas = Vec::new();
    for borrow in two_phase_borrows(body) {
        let Some(activation) = activation(tcx, body, &borrow) else {
            continue;
        };
        let between = locations_between(body, borrow.reservation, activation);
        let window = window_of(tcx, body, &borrow, &between);
        let rewrites = reads_to_redirect(tcx, body, &window, &between);
        formulas.extend(terminators_in(body, &window, &between));
        apply_redirects(tcx, body, rewrites);
    }
    WindowReads { formulas }
}

fn two_phase_borrows<'tcx>(body: &Body<'tcx>) -> Vec<TwoPhaseBorrow<'tcx>> {
    let mut borrows = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for statement_index in 0..data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            borrows.extend(two_phase_borrow_at(body, location));
        }
    }
    borrows
}

/// The reserved place, the blocks of its window and the writes in it that re-point a pointer.
fn window_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    borrow: &TwoPhaseBorrow<'tcx>,
    between: &[Location],
) -> Window<'tcx> {
    let mut finder = RepointFinder {
        tcx,
        body,
        window: borrow.place,
        repoints: Vec::new(),
    };
    for location in between {
        visit_location(body, &mut finder, *location);
    }
    Window {
        temp: borrow.temp,
        place: borrow.place,
        blocks: between.iter().map(|location| location.block).collect(),
        repoints: finder.repoints,
    }
}

/// The terminators in the window with the pointers there, for the formulas they hold.
fn terminators_in<'tcx>(
    body: &Body<'tcx>,
    window: &Window<'tcx>,
    between: &[Location],
) -> Vec<(Span, Window<'tcx>, Pointers)> {
    between
        .iter()
        .filter(|location| {
            location.statement_index == body.basic_blocks[location.block].statements.len()
        })
        .map(|location| {
            let span = body.source_info(*location).span;
            (span, window.clone(), window.pointers_at(body, *location))
        })
        .collect()
}

/// The reads in `between` of a place in the window, with the place each is rewritten to.
fn reads_to_redirect<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    window: &Window<'tcx>,
    between: &[Location],
) -> Vec<(Location, Place<'tcx>, Place<'tcx>)> {
    let length_arguments = &length_arguments(body);
    let mut rewrites = Vec::new();
    for &location in between {
        let mut finder = ReadFinder {
            reads: Vec::new(),
            shape_only: false,
            length_arguments,
            assigns_length_argument: false,
        };
        visit_location(body, &mut finder, location);
        let pointers = window.pointers_at(body, location);
        for (read, shape_only) in finder.reads {
            match window.reading(tcx, body, read, shape_only, pointers) {
                Reading::Native => {}
                Reading::Through(through) => {
                    let span = body.source_info(location).span;
                    refuse_unsupported_path(tcx, body, window.place, span);
                    rewrites.push((location, read, through));
                }
                Reading::Refused(reason) => fatal_at(tcx, body, location, reason),
            }
        }
    }
    rewrites
}

/// The locals that are used only to read the length of what a reference points to
/// (`_len = PtrMetadata(move _r)`), which reads nothing else.
fn length_arguments(body: &Body<'_>) -> HashSet<Local> {
    let mut locals = HashSet::new();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let Some((_, mir::Rvalue::UnaryOp(mir::UnOp::PtrMetadata, operand))) =
                statement.kind.as_assign()
            else {
                continue;
            };
            let Some(local) = operand.place().and_then(|place| place.as_local()) else {
                continue;
            };
            // The assignment and this read are its only uses.
            if use_locations(body, local).len() == 2 {
                locals.insert(local);
            }
        }
    }
    locals
}

fn apply_redirects<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    rewrites: Vec<(Location, Place<'tcx>, Place<'tcx>)>,
) {
    for (location, from, to) in rewrites {
        let mut redirect = Redirect { tcx, from, to };
        let data = &mut body.basic_blocks.as_mut()[location.block];
        match data.statements.get_mut(location.statement_index) {
            Some(stmt) => redirect.visit_statement(stmt, location),
            None => redirect.visit_terminator(data.terminator_mut(), location),
        }
    }
}

/// Stops when the reserved place goes through a raw pointer or holds interior mutability, which
/// a read in the window may write through ([`redirect_window_reads`]).
fn refuse_unsupported_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    span: Span,
) {
    let through_raw_pointer = place
        .iter_projections()
        .any(|(base, elem)| elem == PlaceElem::Deref && base.ty(body, tcx).ty.is_raw_ptr());
    let typing_env = mir_ty::TypingEnv::post_analysis(tcx, body.source.def_id());
    let interior_mutable = !place.ty(body, tcx).ty.is_freeze(tcx, typing_env);
    if through_raw_pointer || interior_mutable {
        tcx.dcx().span_fatal(
            span,
            "this reads a place a two-phase mutable borrow has reserved, which goes through a raw \
             pointer or holds interior mutability; Thrust does not support that",
        );
    }
}

/// Rewrites one read place, the whole place of a non-mutating use.
struct Redirect<'tcx> {
    tcx: TyCtxt<'tcx>,
    from: Place<'tcx>,
    to: Place<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for Redirect<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(&mut self, place: &mut Place<'tcx>, context: PlaceContext, location: Location) {
        if *place == self.from && is_read(context) {
            *place = self.to;
            return;
        }
        self.super_place(place, context, location);
    }
}

fn is_read(context: PlaceContext) -> bool {
    match context {
        PlaceContext::NonMutatingUse(NonMutatingUseContext::Projection)
        | PlaceContext::MutatingUse(_)
        | PlaceContext::NonUse(_) => false,
        PlaceContext::NonMutatingUse(_) => true,
    }
}

/// The places read at a location, each with whether only its shape (variant or length) is.
struct ReadFinder<'a, 'tcx> {
    reads: Vec<(Place<'tcx>, bool)>,
    shape_only: bool,
    /// The locals that hold a shared reference only to read the length of what it points to.
    length_arguments: &'a HashSet<Local>,
    assigns_length_argument: bool,
}

impl<'tcx> mir::visit::Visitor<'tcx> for ReadFinder<'_, 'tcx> {
    fn visit_assign(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        location: Location,
    ) {
        self.assigns_length_argument = place
            .as_local()
            .is_some_and(|local| self.length_arguments.contains(&local));
        self.super_assign(place, rvalue, location);
        self.assigns_length_argument = false;
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        self.shape_only = match rvalue {
            mir::Rvalue::Discriminant(_)
            | mir::Rvalue::UnaryOp(mir::UnOp::PtrMetadata, _)
            | mir::Rvalue::RawPtr(mir::RawPtrKind::FakeForPtrMetadata, _) => true,
            mir::Rvalue::Ref(_, mir::BorrowKind::Shared, _) => self.assigns_length_argument,
            _ => false,
        };
        self.super_rvalue(rvalue, location);
        self.shape_only = false;
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if is_read(context) {
            self.reads.push((*place, self.shape_only));
        }
        self.super_place(place, context, location);
    }
}

/// Finds the writes that re-point a pointer the reserved place goes through.
struct RepointFinder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    window: Place<'tcx>,
    repoints: Vec<(Location, Repoint)>,
}

impl<'tcx> mir::visit::Visitor<'tcx> for RepointFinder<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if context.is_mutating_use() {
            self.record(*place, location);
        }
        self.super_place(place, context, location);
    }
}

impl<'tcx> RepointFinder<'_, 'tcx> {
    /// rustc rejects a write in the window that reaches the reserved memory (RFC 2025), and a
    /// write to a place the reserved one goes through ends right before a dereference: it
    /// re-points that pointer. So a write that overlaps the reserved place re-points it, and is
    /// shorter than it.
    fn record(&mut self, written: Place<'tcx>, location: Location) {
        let window = self.window;
        let index_written = window.projection.iter().any(
            |elem| matches!(elem, PlaceElem::Index(index) if written.as_local() == Some(index)),
        );
        if index_written {
            fatal_at(
                self.tcx,
                self.body,
                location,
                "an index of a place a two-phase mutable borrow has reserved is written before \
                 the borrow is used",
            );
        }
        if !places_conflict(
            self.tcx,
            self.body,
            window,
            written,
            PlaceConflictBias::Overlap,
        ) {
            return;
        }
        if written.projection.len() >= window.projection.len() {
            fatal_at(
                self.tcx,
                self.body,
                location,
                "this writes a place a two-phase mutable borrow has reserved before the borrow is \
                 used",
            );
        }
        let kind = match same_prefix(self.body, written, window) {
            Some(false) => return,
            Some(true) => Repoint::Always,
            None => Repoint::Maybe,
        };
        self.repoints.push((location, kind));
    }
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

/// The unique use of the borrow's temporary, which the reservation dominates. `None` when the
/// borrow is never used.
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
