//! What the report reads off the MIR of an analyzed function: the names of its locals, its loops
//! and calls in the order they are written, and the source span of a block or a statement.
//!
//! A local the program does not name (a temporary of the MIR) is named `__tmp_mir_<fn>_<n>`, after
//! the function and its index in the MIR.
//!
//! The analysis rewrites statements in place (`Nop`s, places) and never renumbers blocks or
//! statements, so a block and a statement index recorded during it locate the same code in
//! `optimized_mir`.

use std::collections::{HashMap, HashSet};

use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Local};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

pub struct DefBody<'tcx> {
    pub body: &'tcx mir::Body<'tcx>,
    /// The function's path as an identifier, for the names of its temporaries.
    label: String,
    local_names: HashMap<Local, String>,
    /// For a closure, the captured variable each field of the closure holds.
    captures: HashMap<usize, String>,
    /// The blocks of each loop, by its header, the headers in the order they are written.
    loops: Vec<(BasicBlock, HashSet<BasicBlock>)>,
    innermost_loop: IndexVec<BasicBlock, Option<BasicBlock>>,
    /// The function each call calls, by the block ending in it, and which call to that function
    /// it is in the order they are written, from 1.
    calls: HashMap<BasicBlock, (String, usize)>,
}

/// `path` with every run of characters that cannot be in an identifier replaced by one `_`.
fn identifier(path: &str) -> String {
    let mut out = String::new();
    for c in path.chars() {
        if c.is_alphanumeric() {
            out.push(c);
        } else if !out.ends_with('_') && !out.is_empty() {
            out.push('_');
        }
    }
    out.trim_end_matches('_').to_owned()
}

/// The block ending in each call and the function it calls, in the order they are written.
fn calls(tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> HashMap<BasicBlock, (String, usize)> {
    let mut found: Vec<(BasicBlock, rustc_span::def_id::DefId, Span)> = body
        .basic_blocks
        .iter_enumerated()
        .filter_map(|(bb, data)| {
            let terminator = data.terminator.as_ref()?;
            let mir::TerminatorKind::Call { func, .. } = &terminator.kind else {
                return None;
            };
            let (callee, _) = func.const_fn_def()?;
            Some((bb, callee, terminator.source_info.span.source_callsite()))
        })
        .collect();
    found.sort_by_key(|(bb, _, span)| (span.lo(), *bb));
    let mut counts: HashMap<rustc_span::def_id::DefId, usize> = HashMap::new();
    found
        .into_iter()
        .map(|(bb, callee, _)| {
            let count = counts.entry(callee).or_default();
            *count += 1;
            (bb, (tcx.item_name(callee).to_string(), *count))
        })
        .collect()
}

impl<'tcx> DefBody<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Self {
        let body = tcx.optimized_mir(def.to_def_id());
        // A name bound again (a shadowing `let`) is told apart by the order of the bindings:
        // `b`, then `b@2`.
        let mut bound: Vec<(Local, String, Span)> = Vec::new();
        for info in &body.var_debug_info {
            if let mir::VarDebugInfoContents::Place(place) = info.value {
                if place.projection.is_empty() && bound.iter().all(|(l, _, _)| *l != place.local) {
                    bound.push((place.local, info.name.to_string(), info.source_info.span));
                }
            }
        }
        bound.sort_by_key(|(local, _, span)| (span.lo(), *local));
        let mut local_names = HashMap::new();
        let mut seen: HashMap<String, usize> = HashMap::new();
        for (local, name, _) in bound {
            let n = seen.entry(name.clone()).or_insert(0);
            *n += 1;
            let name = match *n {
                1 => name,
                n => format!("{name}@{n}"),
            };
            local_names.insert(local, name);
        }
        // A closure's first parameter is the closure, `self`, and the fields of its captures are
        // named after the captured variables, as its debug information places them: `acc` at
        // `*((*_1).0)` names field 0.
        let mut captures = HashMap::new();
        if tcx.is_closure_like(def.to_def_id()) {
            let env = Local::from_u32(1);
            local_names.entry(env).or_insert_with(|| "self".to_owned());
            for info in &body.var_debug_info {
                let mir::VarDebugInfoContents::Place(place) = info.value else {
                    continue;
                };
                if place.local != env {
                    continue;
                }
                let field = place.projection.iter().find_map(|p| match p {
                    mir::ProjectionElem::Field(f, _) => Some(f.index()),
                    _ => None,
                });
                if let Some(field) = field {
                    captures
                        .entry(field)
                        .or_insert_with(|| info.name.to_string());
                }
            }
        }
        // A temporary a call's result goes to is named after the call: `g#k`, the result of the
        // `k`-th call to `g`.
        let calls = calls(tcx, body);
        for (bb, (callee, n)) in &calls {
            let Some(mir::TerminatorKind::Call { destination, .. }) =
                body.basic_blocks[*bb].terminator.as_ref().map(|t| &t.kind)
            else {
                continue;
            };
            if destination.projection.is_empty() && destination.local != mir::RETURN_PLACE {
                local_names
                    .entry(destination.local)
                    .or_insert_with(|| format!("{callee}#{n}"));
            }
        }
        let mut loops = natural_loops(body);
        loops.sort_by_key(|(header, _)| {
            let span = body.basic_blocks[*header].terminator().source_info.span;
            (span.source_callsite().lo(), *header)
        });
        let innermost_loop = body
            .basic_blocks
            .indices()
            .map(|bb| {
                loops
                    .iter()
                    .filter(|(_, blocks)| blocks.contains(&bb))
                    .min_by_key(|(_, blocks)| blocks.len())
                    .map(|(header, _)| *header)
            })
            .collect();
        DefBody {
            body,
            label: identifier(&tcx.def_path_str(def.to_def_id())),
            local_names,
            captures,
            loops,
            innermost_loop,
            calls,
        }
    }

    pub fn local_name(&self, local: Local) -> String {
        if local == mir::RETURN_PLACE {
            return "result".to_owned();
        }
        self.local_names
            .get(&local)
            .cloned()
            .unwrap_or_else(|| format!("__tmp_mir_{}_{}", self.label, local.index()))
    }

    /// Which loop of the function the loop with header `bb` is, in the order they are written,
    /// from 1.
    pub fn loop_number(&self, bb: BasicBlock) -> Option<usize> {
        self.loops.iter().position(|(h, _)| *h == bb).map(|i| i + 1)
    }

    /// The local each argument of the call ending block `bb` is, if it is one.
    pub fn call_args(&self, bb: BasicBlock) -> Vec<Option<Local>> {
        let Some(mir::TerminatorKind::Call { args, .. }) = self.terminator(bb).map(|t| &t.kind)
        else {
            return Vec::new();
        };
        args.iter()
            .map(|arg| {
                let place = arg.node.place()?;
                place.projection.is_empty().then_some(place.local)
            })
            .collect()
    }

    /// The function the call ending block `bb` calls, and which call to it the call is.
    pub fn call(&self, bb: BasicBlock) -> Option<&(String, usize)> {
        self.calls.get(&bb)
    }

    /// The name of what `path` holds: `x`, `*r` and `°r` for the current and final values of a
    /// `&mut` (as Thrust's printer writes them), `p.0` for a component, `discriminant(e)`, `e#1.0` for a field of a variant.
    pub fn path_name(&self, path: &crate::refine::VarPath) -> String {
        use crate::refine::PathStep;
        let wrapped = |name: &str| {
            if name.starts_with(['*', '°']) {
                format!("({name})")
            } else {
                name.to_owned()
            }
        };
        let mut name = self.local_name(path.local);
        let mut steps = path.steps.as_slice();
        // A capture of a closure, through the closure behind its reference or by value: `*acc`,
        // `°acc`, `acc`.
        if path.local == Local::from_u32(1) {
            let capture = |i: &usize| self.captures.get(i);
            match steps {
                [PathStep::Current, PathStep::Field(i), rest @ ..] if capture(i).is_some() => {
                    name = format!("*{}", capture(i).unwrap());
                    steps = rest;
                }
                [PathStep::Final, PathStep::Field(i), rest @ ..] if capture(i).is_some() => {
                    name = format!("°{}", capture(i).unwrap());
                    steps = rest;
                }
                [PathStep::Field(i), rest @ ..] if capture(i).is_some() => {
                    name = capture(i).unwrap().clone();
                    steps = rest;
                }
                _ => {}
            }
        }
        for step in steps {
            name = match step {
                PathStep::Current => format!("*{name}"),
                PathStep::Final => format!("°{name}"),
                PathStep::Field(i) => format!("{}.{i}", wrapped(&name)),
                PathStep::Discriminant => format!("discriminant({name})"),
                PathStep::VariantField(v, f) => {
                    format!("{}#{}.{}", wrapped(&name), v.index(), f.index())
                }
            };
        }
        name
    }

    /// The name of the `idx`-th parameter of the function (its local `_{idx + 1}`).
    pub fn param_name(&self, idx: usize) -> String {
        if idx < self.body.arg_count {
            self.local_name(Local::from_usize(idx + 1))
        } else {
            format!("arg{idx}")
        }
    }

    pub fn is_loop_header(&self, bb: BasicBlock) -> bool {
        self.loops.iter().any(|(header, _)| *header == bb)
    }

    pub fn loop_contains(&self, header: BasicBlock, bb: BasicBlock) -> bool {
        self.loops
            .iter()
            .any(|(h, blocks)| *h == header && blocks.contains(&bb))
    }

    pub fn innermost_loop(&self, bb: BasicBlock) -> Option<BasicBlock> {
        self.innermost_loop.get(bb).copied().flatten()
    }

    pub fn terminator(&self, bb: BasicBlock) -> Option<&mir::Terminator<'tcx>> {
        self.body.basic_blocks.get(bb)?.terminator.as_ref()
    }

    /// The span of statement `stmt` of `bb`, or of its terminator, as the user wrote it (the
    /// call site of a macro such as `assert!`).
    pub fn span(&self, bb: BasicBlock, stmt: Option<usize>) -> Option<Span> {
        let data = self.body.basic_blocks.get(bb)?;
        let span = match stmt {
            Some(idx) if idx < data.statements.len() => data.statements[idx].source_info.span,
            _ => data.terminator.as_ref()?.source_info.span,
        };
        Some(span.source_callsite())
    }
}

/// The natural loops of `body`: each target of a back edge (an edge to a block that dominates
/// its source) with the blocks that reach the edge without passing through it.
fn natural_loops(body: &mir::Body<'_>) -> Vec<(BasicBlock, HashSet<BasicBlock>)> {
    let reachable = mir::traversal::reachable_as_bitset(body);
    let dominators = body.basic_blocks.dominators();
    let predecessors = body.basic_blocks.predecessors();
    let mut loops: Vec<(BasicBlock, HashSet<BasicBlock>)> = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if !reachable.contains(bb) {
            continue;
        }
        for header in data.terminator().successors() {
            if !dominators.dominates(header, bb) {
                continue;
            }
            let mut blocks = HashSet::from([header]);
            let mut stack = vec![bb];
            while let Some(b) = stack.pop() {
                if blocks.insert(b) {
                    stack.extend(predecessors[b].iter().copied());
                }
            }
            match loops.iter_mut().find(|(h, _)| *h == header) {
                Some((_, existing)) => existing.extend(blocks),
                None => loops.push((header, blocks)),
            }
        }
    }
    loops
}
