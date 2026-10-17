//! The clauses of the system as the report shows them: where in the code each was made, what
//! obligation it stands for, and its formula over the program's variables.

use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefIndex, LocalDefId};
use rustc_span::Span;

use crate::chc;

use super::body::DefBody;
use super::expr::{self, Expr};
use super::sites::{Names, Owner};

/// Where a clause was made, read from the spans it was made in (see
/// [`crate::chc::debug::SpanFieldsLayer`]).
#[derive(Debug, Clone, Copy, Default)]
pub struct Provenance {
    pub def: Option<LocalDefId>,
    pub bb: Option<BasicBlock>,
    pub stmt: Option<usize>,
}

impl Provenance {
    pub fn of(debug_info: &chc::DebugInfo) -> Self {
        let def = debug_info
            .get("def_index")
            .and_then(|v| v.parse().ok())
            .map(|i: u32| LocalDefId {
                local_def_index: DefIndex::from_u32(i),
            });
        let bb = debug_info
            .get("bb")
            .and_then(|v| v.strip_prefix("bb"))
            .and_then(|v| v.parse().ok())
            .map(BasicBlock::from_u32);
        let stmt = debug_info.get("stmt_idx").and_then(|v| v.parse().ok());
        Provenance { def, bb, stmt }
    }
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub id: chc::ClauseId,
    pub span: Option<Span>,
    pub kind: String,
    pub premises: Vec<Expr>,
    pub conclusion: Expr,
}

impl Constraint {
    pub fn formula(&self) -> String {
        let premises = Expr::and(self.premises.clone());
        if premises.is_true() {
            return self.conclusion.to_string();
        }
        Expr::app("=>", vec![premises, self.conclusion.clone()]).to_string()
    }
}

fn is_panic(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    let path = tcx.def_path_str(def_id);
    path.starts_with("core::panicking::")
        || path.starts_with("std::panicking::")
        || path.starts_with("std::rt::begin_panic")
}

/// What obligation the clause stands for, from the code it was made in and the template its head
/// belongs to.
fn kind(
    tcx: TyCtxt<'_>,
    clause: &chc::Clause,
    provenance: &Provenance,
    body: Option<&DefBody<'_>>,
    names: &Names,
) -> String {
    let head_owner = match clause.head.pred {
        chc::Pred::Var(p) => names.preds.get(&p).map(|info| info.owner),
        _ => None,
    };
    let goal = matches!(&clause.head.pred, chc::Pred::Known(p) if p.is_bottom());
    let span_name = clause.debug_info.get("span").unwrap_or("");
    if matches!(span_name, "def" | "refine_fn_def") || provenance.bb.is_none() {
        return match head_owner {
            Some(Owner::Block { bb, .. }) if bb == mir::START_BLOCK => "function entry".to_owned(),
            _ if goal => "contract check".to_owned(),
            _ => "function".to_owned(),
        };
    }
    if provenance.stmt.is_some() {
        return "statement".to_owned();
    }
    let (Some(body), Some(bb)) = (body, provenance.bb) else {
        return span_name.to_owned();
    };
    let Some(terminator) = body.terminator(bb) else {
        return span_name.to_owned();
    };
    match &terminator.kind {
        mir::TerminatorKind::Return => match head_owner {
            Some(Owner::Contract { ret: true, .. }) => "return value".to_owned(),
            _ if goal => "ensures".to_owned(),
            _ => "return".to_owned(),
        },
        mir::TerminatorKind::Goto { target } if body.is_loop_header(*target) => {
            if body.loop_contains(*target, bb) {
                "loop preservation".to_owned()
            } else {
                "loop entry".to_owned()
            }
        }
        mir::TerminatorKind::Goto { target } => format!("jump to {target:?}"),
        mir::TerminatorKind::SwitchInt { .. } => "branch".to_owned(),
        mir::TerminatorKind::Assert { msg, .. } => match &**msg {
            mir::AssertKind::BoundsCheck { .. } => "bounds check".to_owned(),
            mir::AssertKind::Overflow(op, ..) => format!("overflow check of {op:?}"),
            mir::AssertKind::OverflowNeg(..) => "overflow check of negation".to_owned(),
            mir::AssertKind::DivisionByZero(..) => "division by zero check".to_owned(),
            mir::AssertKind::RemainderByZero(..) => "remainder by zero check".to_owned(),
            _ => "runtime check".to_owned(),
        },
        mir::TerminatorKind::Call { func, .. } => {
            let Some((callee, _)) = func.const_fn_def() else {
                return "call".to_owned();
            };
            if is_panic(tcx, callee) {
                return "assertion".to_owned();
            }
            let callee_name = tcx.def_path_str(callee);
            match head_owner {
                Some(Owner::Contract { def, ret: false }) if def.to_def_id() == callee => {
                    format!("argument of `{callee_name}`")
                }
                _ if goal => format!("precondition of `{callee_name}`"),
                _ => format!("after call to `{callee_name}`"),
            }
        }
        mir::TerminatorKind::Drop { .. } => "drop".to_owned(),
        _ => span_name.to_owned(),
    }
}

/// A union-find over the clause's variables.
struct Classes {
    parent: Vec<usize>,
}

impl Classes {
    fn new(n: usize) -> Self {
        Classes {
            parent: (0..n).collect(),
        }
    }

    fn find(&mut self, v: usize) -> usize {
        if self.parent[v] != v {
            let root = self.find(self.parent[v]);
            self.parent[v] = root;
        }
        self.parent[v]
    }

    fn union(&mut self, a: usize, b: usize) {
        let (a, b) = (self.find(a), self.find(b));
        let (lo, hi) = if a < b { (a, b) } else { (b, a) };
        self.parent[hi] = lo;
    }
}

fn var_sym(v: chc::TermVarIdx) -> String {
    v.to_string()
}

fn var_of(e: &Expr, vars: &HashMap<String, usize>) -> Option<usize> {
    match e {
        Expr::Sym(s) => vars.get(s).copied(),
        _ => None,
    }
}

/// The names the clause's variables may take, best first: what an argument of a predicate of
/// the same function stands for in its template (the body's atoms before the head's), then the
/// program variable a typing environment entry mapped to it. The arguments of another function's
/// predicates are named in that function, so they name nothing here.
fn candidate_names(
    clause: &chc::Clause,
    def: Option<LocalDefId>,
    names: &Names,
    body: Option<&DefBody<'_>>,
) -> Vec<(chc::TermVarIdx, String)> {
    let mut candidates = Vec::new();
    let atoms = clause
        .body
        .atoms
        .iter()
        .chain(std::iter::once(&clause.head));
    for atom in atoms {
        let chc::Pred::Var(p) = atom.pred else {
            continue;
        };
        let Some(info) = names.preds.get(&p) else {
            continue;
        };
        if Some(info.owner.def()) != def {
            continue;
        }
        // `info.args` follows the order the arguments are shown in.
        let shown = names.pred_head(p).arrange(&atom.args);
        for (arg, name) in shown.iter().zip(&info.args) {
            if let (chc::Term::Var(v), Some(name)) = (arg, name) {
                candidates.push((*v, name.clone()));
            }
        }
    }
    let origin = &clause.origin;
    let entries = origin
        .environment
        .iter()
        .chain(&origin.body)
        .chain(std::iter::once(&origin.head));
    for entry in entries {
        for mapping in entry.mappings() {
            let local = mapping
                .source()
                .strip_prefix('_')
                .and_then(|n| n.parse::<usize>().ok());
            if let (Some(local), Some(body)) = (local, body) {
                let name = body.local_name(mir::Local::from_usize(local));
                candidates.push((mapping.chc_var(), name));
            }
        }
    }
    candidates
}

/// The clause as premises and a conclusion over named variables: variables equal to one another
/// are merged, a variable without a name that a premise defines is replaced by its definition,
/// and a goal's negated premise becomes its conclusion.
fn render(
    id: chc::ClauseId,
    clause: &chc::Clause,
    def: Option<LocalDefId>,
    names: &Names,
    body: Option<&DefBody<'_>>,
) -> (Vec<Expr>, Expr) {
    let pred_name = |p| names.pred_head(p);
    // A variable of the clause the program does not name: `__tmp_chc_c<clause>_<n>`.
    let unnamed_name = |class: usize| format!("__tmp_chc_{id:?}_{class}");
    let sym = |v: &chc::TermVarIdx| var_sym(*v);
    let mut premises: Vec<Expr> = clause
        .body
        .atoms
        .iter()
        .filter(|a| !matches!(a.pred, chc::Pred::Var(p) if names.always_true.contains(&p)))
        .map(|a| expr::of_atom(a, &sym, &pred_name))
        .chain(expr::of_formula(&clause.body.formula, &sym, &pred_name).into_conjuncts())
        .flat_map(|e| e.normalize().into_conjuncts())
        .collect();
    let mut conclusion = expr::of_atom(&clause.head, &sym, &pred_name).normalize();

    let vars: HashMap<String, usize> = clause
        .vars
        .indices()
        .map(|v| (var_sym(v), v.index()))
        .collect();
    let mut classes = Classes::new(clause.vars.len());
    premises.retain(|p| match p {
        Expr::App(f, args) if f == "=" && args.len() == 2 => {
            match (var_of(&args[0], &vars), var_of(&args[1], &vars)) {
                (Some(a), Some(b)) => {
                    classes.union(a, b);
                    false
                }
                _ => true,
            }
        }
        _ => true,
    });

    let mut class_name: BTreeMap<usize, String> = BTreeMap::new();
    let mut used = HashSet::new();
    let mut candidates = candidate_names(clause, def, names, body);
    // Of two names of one value, a variable's own reads better than its entry value's `old(x)`.
    candidates.sort_by_key(|(_, name)| name.starts_with("old("));
    for (v, name) in candidates {
        let class = classes.find(v.index());
        if class_name.contains_key(&class) || used.contains(&name) {
            continue;
        }
        used.insert(name.clone());
        class_name.insert(class, name);
    }
    let mut subst: HashMap<String, Expr> = HashMap::new();
    for v in clause.vars.indices() {
        let class = classes.find(v.index());
        let name = class_name
            .get(&class)
            .cloned()
            .unwrap_or_else(|| unnamed_name(class));
        subst.insert(var_sym(v), Expr::sym(name));
    }
    premises = premises.iter().map(|p| p.subst(&subst)).collect();
    conclusion = conclusion.subst(&subst);

    // Replace each unnamed variable a premise defines by its definition.
    let unnamed: HashSet<String> = clause
        .vars
        .indices()
        .map(|v| classes.find(v.index()))
        .filter(|class| !class_name.contains_key(class))
        .map(unnamed_name)
        .collect();
    while let Some((i, var, definition)) = premises.iter().enumerate().find_map(|(i, p)| {
        let Expr::App(f, args) = p else {
            return None;
        };
        if f != "=" || args.len() != 2 {
            return None;
        }
        [(&args[0], &args[1]), (&args[1], &args[0])]
            .into_iter()
            .find_map(|(lhs, rhs)| match lhs {
                Expr::Sym(s) if unnamed.contains(s) && !rhs.mentions(s) => {
                    Some((i, s.clone(), rhs.clone()))
                }
                _ => None,
            })
    }) {
        premises.remove(i);
        let one = HashMap::from([(var, definition)]);
        premises = premises.iter().map(|p| p.subst(&one)).collect();
        conclusion = conclusion.subst(&one);
    }

    // A goal's last premise is the negated property it checks.
    if conclusion.is_false() {
        if let Some(last) = premises.pop() {
            conclusion = Expr::app("not", vec![last]);
        }
    }
    let premises: Vec<Expr> = premises
        .into_iter()
        .flat_map(|p| p.normalize().into_conjuncts())
        .collect();
    let conclusion = conclusion.normalize();
    (premises, conclusion)
}

pub fn constraint(
    tcx: TyCtxt<'_>,
    id: chc::ClauseId,
    clause: &chc::Clause,
    names: &Names,
    body: Option<&DefBody<'_>>,
) -> Constraint {
    let provenance = Provenance::of(&clause.debug_info);
    let span = match (body, provenance.bb) {
        (Some(body), Some(bb)) => body.span(bb, provenance.stmt),
        _ => provenance
            .def
            .map(|def| tcx.def_span(def.to_def_id()).source_callsite()),
    };
    let kind = kind(tcx, clause, &provenance, body, names);
    let (premises, conclusion) = render(id, clause, provenance.def, names, body);
    Constraint {
        id,
        span,
        kind,
        premises,
        conclusion,
    }
}
