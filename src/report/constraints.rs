//! The clauses of the system as the report shows them: where in the code each was made, what
//! obligation it stands for, and its formula over the program's variables.

use std::collections::{BTreeMap, HashMap, HashSet};

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, DefIndex, LocalDefId};
use rustc_span::Span;

use crate::analyze::ContractAnnotations;
use crate::chc;
use crate::refine::VarPath;

use super::body::DefBody;
use super::formula::{self, show, Formula, Name, Term};
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
        let def = debug_info.number("def_index").map(|i| LocalDefId {
            local_def_index: DefIndex::from_u32(i as u32),
        });
        let bb = debug_info
            .number("bb_index")
            .map(|i| BasicBlock::from_u32(i as u32));
        let stmt = debug_info.number("stmt_idx").map(|i| i as usize);
        Provenance { def, bb, stmt }
    }

    /// The span of the code the clause was made at: its statement or terminator, or else its
    /// function.
    pub fn span(&self, tcx: TyCtxt<'_>) -> Option<Span> {
        let def = self.def?.to_def_id();
        let body = tcx.is_mir_available(def).then(|| tcx.optimized_mir(def));
        let in_body = body
            .zip(self.bb)
            .and_then(|(body, bb)| super::body::span_in(body, bb, self.stmt));
        Some(in_body.unwrap_or_else(|| tcx.def_span(def).source_callsite()))
    }
}

#[derive(Debug, Clone)]
pub struct Constraint {
    pub id: chc::ClauseId,
    pub span: Option<Span>,
    pub kind: String,
    pub premises: Vec<String>,
    pub conclusion: String,
    /// The premises implying the conclusion.
    pub formula: String,
    /// The name of each variable of the clause, by its index.
    pub vars: Vec<String>,
    pub annotation: Annotation,
}

/// The written annotation a constraint checks or assumes, by its spans.
#[derive(Debug, Clone, Default)]
pub enum Annotation {
    #[default]
    None,
    /// The goal checks it: an `ensures` at a return, a `requires` at a call.
    Checks(Vec<Span>),
    /// The result of a call to the function, as its `ensures` states it.
    Assumes(DefId, Vec<Span>),
}

/// Whether `def_id` is one of the functions a panic calls: the panic language items (those of
/// `assert!`, `panic!`, a failed bounds or overflow check) and `std::rt::begin_panic`.
fn is_panic(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    use rustc_hir::LangItem;
    let lang_item = tcx.as_lang_item(def_id);
    let panics = matches!(
        lang_item,
        Some(
            LangItem::Panic
                | LangItem::PanicNounwind
                | LangItem::PanicFmt
                | LangItem::PanicDisplay
                | LangItem::ConstPanicFmt
                | LangItem::PanicBoundsCheck
                | LangItem::PanicMisalignedPointerDereference
                | LangItem::PanicCannotUnwind
                | LangItem::PanicInCleanup
                | LangItem::PanicAddOverflow
                | LangItem::PanicSubOverflow
                | LangItem::PanicMulOverflow
                | LangItem::PanicDivOverflow
                | LangItem::PanicRemOverflow
                | LangItem::PanicNegOverflow
                | LangItem::PanicShrOverflow
                | LangItem::PanicShlOverflow
        )
    );
    panics || tcx.is_diagnostic_item(rustc_span::sym::begin_panic, def_id)
}

/// What obligation the clause stands for, from the code it was made in and the template its head
/// belongs to, and the written annotation it checks or assumes.
fn kind(
    tcx: TyCtxt<'_>,
    clause: &chc::Clause,
    provenance: &Provenance,
    body: Option<&DefBody<'_>>,
    names: &Names,
    annotations: &HashMap<DefId, ContractAnnotations>,
) -> (String, Annotation) {
    let plain = |kind: String| (kind, Annotation::None);
    let head_owner = match clause.head.pred {
        chc::Pred::Var(p) => names.preds.get(&p).map(|info| info.owner),
        _ => None,
    };
    let goal = matches!(&clause.head.pred, chc::Pred::Known(p) if p.is_bottom());
    let span_name = clause.debug_info.get("span").unwrap_or("");
    if matches!(span_name, "def" | "refine_fn_def") || provenance.bb.is_none() {
        return plain(match head_owner {
            Some(Owner::Block { bb, .. }) if bb == mir::START_BLOCK => "function entry".to_owned(),
            _ if goal => "contract check".to_owned(),
            _ => "function".to_owned(),
        });
    }
    if provenance.stmt.is_some() {
        return plain("statement".to_owned());
    }
    let (Some(body), Some(bb)) = (body, provenance.bb) else {
        return plain(span_name.to_owned());
    };
    let Some(terminator) = body.terminator(bb) else {
        return plain(span_name.to_owned());
    };
    // A method without a contract of its own has that of the trait method it implements.
    let written = |def_id: DefId| {
        let trait_item = || tcx.opt_associated_item(def_id)?.trait_item_def_id;
        annotations
            .get(&def_id)
            .or_else(|| annotations.get(&trait_item()?))
    };
    let kind = match &terminator.kind {
        mir::TerminatorKind::Return => match head_owner {
            Some(Owner::Contract { ret: true, .. }) => "return value".to_owned(),
            _ if goal => {
                let ensures = provenance.def.and_then(|def| written(def.to_def_id()));
                let spans = ensures.map(|a| a.ensures.clone()).unwrap_or_default();
                return ("ensures".to_owned(), Annotation::Checks(spans));
            }
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
                return plain("call".to_owned());
            };
            if is_panic(tcx, callee) {
                return plain("assertion".to_owned());
            }
            let callee_name = tcx.def_path_str(callee);
            match head_owner {
                // The callee's contract, or that of the method a call to a trait method resolves
                // to.
                Some(Owner::Contract { def, ret: false }) => {
                    format!("argument of `{}`", tcx.def_path_str(def.to_def_id()))
                }
                _ if goal => {
                    let spans = written(callee).map(|a| a.requires.clone());
                    return (
                        format!("precondition of `{callee_name}`"),
                        Annotation::Checks(spans.unwrap_or_default()),
                    );
                }
                _ => {
                    let kind = format!("after call to `{callee_name}`");
                    return match written(callee).filter(|a| !a.ensures.is_empty()) {
                        Some(a) => (kind, Annotation::Assumes(callee, a.ensures.clone())),
                        None => plain(kind),
                    };
                }
            }
        }
        mir::TerminatorKind::Drop { .. } => "drop".to_owned(),
        _ => span_name.to_owned(),
    };
    plain(kind)
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

/// The two sides of `f` if it is an equation.
fn equation<V>(f: &chc::Formula<V>) -> Option<(&chc::Term<V>, &chc::Term<V>)> {
    match f {
        chc::Formula::Atom(chc::Atom {
            guard: None,
            pred: chc::Pred::Known(p),
            args,
        }) if *p == chc::KnownPred::EQUAL && args.len() == 2 => Some((&args[0], &args[1])),
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
        let shown = names.arrange(p, &atom.args);
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
            let path = mapping.var().and_then(path_of);
            if let (Some(path), Some(body)) = (path, body) {
                candidates.push((mapping.chc_var(), body.path_name(&path)));
            }
        }
    }
    candidates
}

/// What a variable of the analysis holds, as the code that made it described it, or as the local
/// it is.
pub fn path_of(var: &chc::debug::ErasedVar) -> Option<VarPath> {
    use crate::refine::Var;
    if let Some(path) = var.downcast_ref::<VarPath>() {
        return Some(path.clone());
    }
    let free = |v: &crate::rty::RefinedTypeVar<Var>| match v {
        crate::rty::RefinedTypeVar::Free(v) => Some(*v),
        _ => None,
    };
    let var = match var.downcast_ref::<Var>() {
        Some(var) => *var,
        None => free(var.downcast_ref::<crate::rty::RefinedTypeVar<Var>>()?)?,
    };
    match var {
        Var::Local(local) => Some(VarPath {
            local,
            steps: Vec::new(),
        }),
        Var::Temp(_) => None,
    }
}

/// The clause as premises and a conclusion over named variables, and the name of each variable: variables equal to one another
/// are merged, a variable without a name that a premise defines is replaced by its definition,
/// and a goal's negated premise becomes its conclusion.
fn render(
    id: chc::ClauseId,
    clause: &chc::Clause,
    def: Option<LocalDefId>,
    names: &Names,
    body: Option<&DefBody<'_>>,
) -> (Vec<Formula>, Formula, Vec<Name>) {
    let mut premises: Vec<chc::Formula> = clause
        .body
        .atoms
        .iter()
        .filter(|a| !matches!(a.pred, chc::Pred::Var(p) if names.always_true.contains(&p)))
        .cloned()
        .map(chc::Formula::Atom)
        .chain(chc::conjuncts(&clause.body.formula))
        .flat_map(|f| chc::conjuncts(&formula::tidy(f)))
        .collect();

    let mut classes = Classes::new(clause.vars.len());
    premises.retain(|p| match equation(p) {
        Some((chc::Term::Var(a), chc::Term::Var(b))) => {
            classes.union(a.index(), b.index());
            false
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
    // A variable of the clause the program does not name: `__tmp_chc_c<clause>_<n>`.
    let mut unnamed = HashSet::new();
    let var_names: Vec<Name> = clause
        .vars
        .indices()
        .map(|v| {
            let class = classes.find(v.index());
            match class_name.get(&class) {
                Some(name) => Name::new(name),
                None => {
                    let name = Name::new(&format!("__tmp_chc_{id:?}_{class}"));
                    unnamed.insert(name);
                    name
                }
            }
        })
        .collect();
    let rename = |f: chc::Formula| f.map_var(|v| var_names[v.index()]);
    let mut premises: Vec<Formula> = premises.into_iter().map(rename).collect();
    let mut conclusion = rename(clause.head.clone().into());

    // Replace each unnamed variable a premise defines by its definition.
    let definition = |p: &Formula| {
        let (a, b) = equation(p)?;
        [(a, b), (b, a)]
            .into_iter()
            .find_map(|(lhs, rhs)| match lhs {
                Term::Var(v) if unnamed.contains(v) && rhs.fv().all(|w| w != v) => {
                    Some((*v, rhs.clone()))
                }
                _ => None,
            })
    };
    while let Some((i, (var, def))) = premises
        .iter()
        .enumerate()
        .find_map(|(i, p)| Some((i, definition(p)?)))
    {
        premises.remove(i);
        let subst = |f: Formula| f.subst_var(|v| if v == var { def.clone() } else { Term::Var(v) });
        premises = premises.into_iter().map(subst).collect();
        conclusion = subst(conclusion);
    }

    // Tidied as one conjunction, as the formula shown is.
    let mut premises: Vec<Formula> = formula::equalities(
        premises
            .into_iter()
            .flat_map(|f| chc::conjuncts(&formula::tidy(f)))
            .collect(),
    );
    let mut conclusion = formula::tidy(conclusion);
    // A goal's last premise is the negated property it checks.
    if conclusion.is_bottom() {
        if let Some(last) = premises.pop() {
            conclusion = last.not();
        }
    }
    // A premise equating a term with itself says nothing, and one said before says it again.
    premises.retain(|p| !matches!(equation(p), Some((a, b)) if a == b));
    let mut said: Vec<Formula> = Vec::new();
    premises.retain(|p| {
        let again = said.contains(p);
        said.push(p.clone());
        !again
    });
    (premises, conclusion, var_names)
}

pub fn constraint(
    tcx: TyCtxt<'_>,
    id: chc::ClauseId,
    clause: &chc::Clause,
    names: &Names,
    body: Option<&DefBody<'_>>,
    annotations: &HashMap<DefId, ContractAnnotations>,
) -> Constraint {
    let provenance = Provenance::of(&clause.debug_info);
    let span = provenance.span(tcx);
    let (kind, annotation) = kind(tcx, clause, &provenance, body, names, annotations);
    let (premises, conclusion, vars) = render(id, clause, provenance.def, names, body);
    let formula = show(
        &formula::and(premises.clone()).implies(conclusion.clone()),
        names,
    );
    Constraint {
        id,
        span,
        kind,
        premises: premises.iter().map(|p| show(p, names)).collect(),
        conclusion: show(&conclusion, names),
        formula,
        vars: vars.iter().map(|v| v.as_str().to_owned()).collect(),
        annotation,
    }
}
