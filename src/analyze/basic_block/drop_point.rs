use std::collections::{BTreeSet, HashMap};

use rustc_abi::FieldIdx;
use rustc_index::bit_set::{DenseBitSet, MixedBitSet};
use rustc_middle::mir::{self, BasicBlock, Body, Local};
use rustc_middle::ty::{self as mir_ty, TyCtxt};
use rustc_mir_dataflow::{
    impls::{MaybeLiveLocals, MaybeUninitializedPlaces},
    move_paths::{MoveData, MovePathIndex},
    ResultsCursor,
};

/// The parts of a dropped local that were moved out before its drop point, as paths of field
/// indices from the local. A part is cut at its first projection other than a field, so a move
/// out of an enum variant or through a `Box` names the enum or the box.
pub type MovedOut = Vec<Vec<FieldIdx>>;

#[derive(Debug, Clone, Default)]
pub struct DropPoints {
    // TODO: ad-hoc
    pub before_statements: Vec<Local>,
    after_statements: Vec<DenseBitSet<Local>>,
    after_terminator: HashMap<BasicBlock, DenseBitSet<Local>>,
    /// Locals dropped after the terminator regardless of the target, in
    /// addition to the liveness-derived sets above. A set, since the same local
    /// must not be dropped twice; ordered by index to keep drops deterministic.
    after_terminator_extra: BTreeSet<Local>,
    /// The parts moved out of a local dropped after the statement (or, at the number of
    /// statements, the terminator) of the index; a local dropped whole has no entry.
    moved_out: HashMap<(usize, Local), MovedOut>,
}

impl DropPoints {
    pub fn builder<'mir, 'tcx>(body: &'mir Body<'tcx>) -> DropPointsBuilder<'mir, 'tcx> {
        DropPointsBuilder {
            body,
            bb_ins_cache: HashMap::new(),
        }
    }

    pub fn position(&self, local: Local) -> Option<usize> {
        self.after_statements
            .iter()
            .position(|s| s.contains(local))
            .or_else(|| {
                self.is_after_terminator(local)
                    .then_some(self.after_statements.len())
            })
    }

    fn is_after_terminator(&self, local: Local) -> bool {
        self.after_terminator.values().any(|s| s.contains(local))
            || self.after_terminator_extra.contains(&local)
    }

    pub fn remove_after_statement(&mut self, statement_index: usize, local: Local) -> bool {
        self.after_statements[statement_index].remove(local)
    }

    pub fn insert_after_statement(&mut self, statement_index: usize, local: Local) -> bool {
        self.after_statements[statement_index].insert(local)
    }

    pub fn after_statement(&self, statement_index: usize) -> DenseBitSet<Local> {
        self.after_statements[statement_index].clone()
    }

    pub fn insert_after_terminator(&mut self, local: Local) {
        self.after_terminator_extra.insert(local);
    }

    pub fn moved_out(&self, statement_index: usize, local: Local) -> MovedOut {
        self.moved_out
            .get(&(statement_index, local))
            .cloned()
            .unwrap_or_default()
    }

    pub fn terminator_index(&self) -> usize {
        self.after_statements.len() - 1
    }

    pub fn after_terminator(&self, target: &BasicBlock) -> Vec<Local> {
        let mut t = self.after_terminator[target].clone();
        t.union(self.after_statements.last().unwrap());
        t.iter()
            .chain(self.after_terminator_extra.iter().copied())
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct DropPointsBuilder<'mir, 'tcx> {
    body: &'mir Body<'tcx>,
    bb_ins_cache: HashMap<BasicBlock, DenseBitSet<Local>>,
}

/// Whether a value of `ty` may hold a `&mut`, whose prophecy its drop would resolve.
fn may_hold_mut_ref<'tcx>(tcx: TyCtxt<'tcx>, ty: mir_ty::Ty<'tcx>) -> bool {
    let mut visited = std::collections::HashSet::new();
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        if !visited.insert(ty) {
            continue;
        }
        for ty in ty.walk().filter_map(|arg| arg.as_type()) {
            match ty.kind() {
                mir_ty::TyKind::Ref(_, _, m) if m.is_mut() => return true,
                mir_ty::TyKind::Adt(adt, args) => {
                    pending.extend(adt.all_fields().map(|field| field.ty(tcx, args)));
                }
                _ => {}
            }
        }
    }
    false
}

/// The parts of `local` that may be uninitialized (`uninit`) and may hold a `&mut`, which its drop
/// must not resolve: their pairs went with the move. A `&mut` itself is never one, since a moved
/// `&mut` becomes a reborrow and the source still resolves to it.
fn moved_out_parts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    move_data: &MoveData<'tcx>,
    uninit: &MixedBitSet<MovePathIndex>,
    local: Local,
) -> MovedOut {
    let Some(root) = move_data.rev_lookup.find_local(local) else {
        return MovedOut::new();
    };
    let mut parts = MovedOut::new();
    let mut pending = vec![root];
    while let Some(mpi) = pending.pop() {
        let path = &move_data.move_paths[mpi];
        let ty = path.place.ty(body, tcx).ty;
        if !uninit.contains(mpi) || ty.is_ref() || !may_hold_mut_ref(tcx, ty) {
            pending.extend(path.children(&move_data.move_paths).map(|(child, _)| child));
            continue;
        }
        let fields = path
            .place
            .projection
            .iter()
            .map_while(|elem| match elem {
                mir::PlaceElem::Field(idx, _) => Some(idx),
                _ => None,
            })
            .collect();
        parts.push(fields);
    }
    let all = parts.clone();
    parts.retain(|part| {
        !all.iter()
            .any(|other| other.len() < part.len() && part.starts_with(other))
    });
    parts.sort();
    parts.dedup();
    parts
}

/// What a drop point needs of the moves: the move paths and which of them may be uninitialized.
pub struct MoveState<'a, 'mir, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub move_data: &'a MoveData<'tcx>,
    pub uninit: &'a mut ResultsCursor<'mir, 'tcx, MaybeUninitializedPlaces<'mir, 'tcx>>,
}

/// Locals whose ownership is fully transferred away by the statement (or
/// terminator) at `statement_index`. Such a local is left uninitialized, so its
/// drop obligation (including resolving any mutable-borrow prophecies it owns)
/// moves to the destination and it must not be dropped at the move site.
///
/// Only owned (non-reference) operands are reported: `move`d references are
/// turned into reborrows by `ReborrowVisitor`/`RustCallVisitor`, so the source
/// local remains live and must still be dropped.
fn moved_locals<'tcx>(
    body: &Body<'tcx>,
    bb: BasicBlock,
    statement_index: usize,
) -> DenseBitSet<Local> {
    struct Visitor<'a, 'tcx> {
        body: &'a Body<'tcx>,
        locals: DenseBitSet<Local>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Visitor<'_, 'tcx> {
        fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, _location: mir::Location) {
            if let mir::Operand::Move(place) = operand {
                if place.projection.is_empty() && !self.body.local_decls[place.local].ty.is_ref() {
                    self.locals.insert(place.local);
                }
            }
        }
    }
    let mut visitor = Visitor {
        body,
        locals: DenseBitSet::new_empty(body.local_decls.len()),
    };
    let loc = mir::Location {
        statement_index,
        block: bb,
    };
    let data = &body.basic_blocks[bb];
    use mir::visit::Visitor as _;
    if statement_index < data.statements.len() {
        visitor.visit_statement(&data.statements[statement_index], loc);
    } else if let Some(tmnt) = &data.terminator {
        visitor.visit_terminator(tmnt, loc);
    }
    visitor.locals
}

fn def_local<'tcx>(data: &mir::BasicBlockData<'tcx>, statement_index: usize) -> Option<Local> {
    struct Visitor {
        local: Option<Local>,
    }
    impl<'tcx> mir::visit::Visitor<'tcx> for Visitor {
        fn visit_local(
            &mut self,
            local: Local,
            ctxt: mir::visit::PlaceContext,
            _location: mir::Location,
        ) {
            if ctxt.is_place_assignment() {
                let old = self.local.replace(local);
                assert!(old.is_none());
            }
        }
    }
    let mut visitor = Visitor { local: None };
    let loc = mir::Location::START;
    use mir::visit::Visitor as _;
    if statement_index < data.statements.len() {
        visitor.visit_statement(&data.statements[statement_index], loc);
    } else if let Some(tmnt) = &data.terminator {
        visitor.visit_terminator(tmnt, loc);
    }
    visitor.local
}

/// The parts moved out of each local dropped in `bb`, by drop point (see [`DropPoints`]).
fn moved_out_at_drops<'tcx>(
    moves: &mut MoveState<'_, '_, 'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    after_statements: &[DenseBitSet<Local>],
    after_terminator: &HashMap<BasicBlock, DenseBitSet<Local>>,
) -> HashMap<(usize, Local), MovedOut> {
    let data = &body.basic_blocks[bb];
    let terminator_index = data.statements.len();
    let mut at_terminator = after_statements[terminator_index].clone();
    for edge_drops in after_terminator.values() {
        at_terminator.union(edge_drops);
    }
    let mut moved_out = HashMap::new();
    for (statement_index, locals) in after_statements.iter().enumerate() {
        let locals = if statement_index == terminator_index {
            &at_terminator
        } else {
            locals
        };
        if locals.is_empty() {
            continue;
        }
        let location = mir::Location {
            statement_index,
            block: bb,
        };
        let at_terminator = statement_index == terminator_index;
        // The dataflow takes the place of a `Drop` terminator as uninitialized after it, but
        // that drop is the one made here.
        let is_drop =
            at_terminator && matches!(data.terminator().kind, mir::TerminatorKind::Drop { .. });
        if is_drop {
            moves.uninit.seek_before_primary_effect(location);
        } else {
            moves.uninit.seek_after_primary_effect(location);
        }
        // A call initializes its destination on the return edge, after its primary effect.
        let destination = match &data.terminator().kind {
            mir::TerminatorKind::Call { destination, .. } if at_terminator => {
                Some(destination.local)
            }
            _ => None,
        };
        for local in locals.iter().filter(|local| Some(*local) != destination) {
            let parts =
                moved_out_parts(moves.tcx, body, moves.move_data, moves.uninit.get(), local);
            if !parts.is_empty() {
                moved_out.insert((statement_index, local), parts);
            }
        }
    }
    moved_out
}

impl<'mir, 'tcx> DropPointsBuilder<'mir, 'tcx> {
    pub fn build(
        &mut self,
        results: &mut ResultsCursor<'mir, 'tcx, MaybeLiveLocals>,
        moves: &mut MoveState<'_, '_, 'tcx>,
        bb: BasicBlock,
    ) -> DropPoints {
        let data = &self.body.basic_blocks[bb];

        let mut after_terminator = HashMap::new();
        let mut after_statements = Vec::new();
        after_statements.resize_with(data.statements.len() + 1, || DenseBitSet::new_empty(0));

        results.seek_to_block_end(bb);
        let live_locals_after_terminator = results.get().clone();

        use rustc_data_structures::graph::Successors as _;
        let mut ins = DenseBitSet::new_empty(self.body.local_decls.len());
        for succ_bb in self.body.basic_blocks.successors(bb) {
            self.bb_ins_cache.entry(succ_bb).or_insert_with(|| {
                results.seek_to_block_start(succ_bb);
                results.get().clone()
            });
            let edge_drops = {
                let mut t = live_locals_after_terminator.clone();
                t.subtract(&self.bb_ins_cache[&succ_bb]);
                t
            };
            after_terminator.insert(succ_bb, edge_drops);
            ins.union(&self.bb_ins_cache[&succ_bb]);
        }

        tracing::debug!(?live_locals_after_terminator, ?ins);
        // FIXME: isn't it appropriate to use live_locals_after_terminator here? but it lacks
        //        some locals from successor ins...
        let mut last_live_locals = ins;
        // TODO: we may use seek_before_primary_effect here
        for statement_index in (0..=data.statements.len()).rev() {
            let loc = mir::Location {
                statement_index,
                block: bb,
            };
            results.seek_after_primary_effect(loc);
            let live_locals = results.get().clone();
            tracing::debug!(?live_locals, ?loc);
            after_statements[statement_index] = {
                let mut t = live_locals.clone();
                if let Some(def) = def_local(data, statement_index) {
                    t.insert(def);
                }
                t.subtract(&last_live_locals);
                t.subtract(&moved_locals(self.body, bb, statement_index));
                t
            };
            last_live_locals = live_locals;
        }

        self.bb_ins_cache.insert(bb, last_live_locals.clone());

        let moved_out =
            moved_out_at_drops(moves, self.body, bb, &after_statements, &after_terminator);

        tracing::info!(
            ?bb,
            ?after_statements,
            ?after_terminator,
            "analyzed implicit drop points"
        );
        DropPoints {
            before_statements: Default::default(),
            after_statements,
            after_terminator,
            after_terminator_extra: Default::default(),
            moved_out,
        }
    }
}
