//! Candidate atoms for a loop head's predicate variable, instantiated from contracts.
//!
//! With `THRUST_CANDIDATE_ATOMS=1`, each conjunct of a contract that the loop's function or a
//! callee in the loop states is instantiated at the terms over the loop head's arguments, sort by
//! sort (liquid types' qualifier instantiation), and the instances are declared as candidates of
//! the head's predicate variable. They are hints for the solver's hypothesis space and are never
//! asserted, so they do not change the set of solutions.

use std::collections::HashMap;

use super::*;

/// How deep the terms over a head argument go (`cur`, `final`, a tuple field; a box, which
/// the emitted system does not have, is not counted).
const TERM_DEPTH: usize = 3;

/// The candidate atoms declared for one predicate variable, over its arguments by position.
#[derive(Debug, Clone)]
pub struct CandidateAtoms {
    pub pred: PredVarId,
    pub atoms: Vec<Formula>,
}

/// The terms over a predicate variable's arguments, each with its sort.
#[derive(Debug, Clone)]
pub struct HeadTerms {
    terms: Vec<(Term, Sort)>,
}

impl HeadTerms {
    pub fn new(sig: &[Sort]) -> Self {
        let mut terms = Vec::new();
        for (idx, sort) in sig.iter().enumerate() {
            push_projections(
                &mut terms,
                Term::var(TermVarIdx::from_usize(idx)),
                sort.clone(),
                TERM_DEPTH,
            );
        }
        HeadTerms { terms }
    }

    fn of_sort<'a>(&'a self, sort: &'a Sort) -> impl Iterator<Item = &'a Term> + 'a {
        self.terms
            .iter()
            .filter(move |(_, s)| s == sort)
            .map(|(t, _)| t)
    }

    /// The terms a contract variable of `sort` is instantiated at: the head terms of that sort,
    /// and for a reference, the reference built from head terms of its target sort, so that
    /// `*r` and `^r` of a callee's `&mut` parameter can land on a field of a head argument.
    fn fillers(&self, sort: &Sort) -> Vec<Term> {
        let mut fillers: Vec<Term> = self.of_sort(sort).cloned().collect();
        match sort {
            Sort::Mut(inner) => {
                let targets: Vec<Term> = self.of_sort(inner).cloned().collect();
                for current in &targets {
                    for final_ in &targets {
                        fillers.push(Term::mut_(current.clone(), final_.clone()));
                    }
                }
            }
            Sort::Box(inner) => {
                fillers.extend(self.fillers(inner).into_iter().map(Term::box_));
            }
            _ => {}
        }
        fillers
    }

    /// `^x = ^y` for every two head terms of the same `&mut` sort: the prophecy of a reference
    /// that the loop carries along with its entry value.
    pub fn prophecy_atoms(&self) -> Vec<Formula> {
        let mut atoms = Vec::new();
        for (i, (x, xs)) in self.terms.iter().enumerate() {
            if !matches!(xs, Sort::Mut(_)) {
                continue;
            }
            for (y, ys) in &self.terms[i + 1..] {
                if xs == ys {
                    let atom = x.clone().mut_final().equal_to(y.clone().mut_final());
                    atoms.push(Formula::Atom(atom));
                }
            }
        }
        atoms
    }
}

fn push_projections(terms: &mut Vec<(Term, Sort)>, term: Term, sort: Sort, depth: usize) {
    terms.push((term.clone(), sort.clone()));
    if let Sort::Box(inner) = sort {
        push_projections(terms, term.box_current(), *inner, depth);
        return;
    }
    if depth == 0 {
        return;
    }
    match sort {
        Sort::Mut(inner) => {
            push_projections(
                terms,
                term.clone().mut_current(),
                (*inner).clone(),
                depth - 1,
            );
            push_projections(terms, term.mut_final(), *inner, depth - 1);
        }
        Sort::Tuple(elems) => {
            for (i, elem) in elems.into_iter().enumerate() {
                push_projections(terms, term.clone().tuple_proj(i), elem, depth - 1);
            }
        }
        _ => {}
    }
}

/// The top-level conjuncts of `formula`.
pub fn conjuncts<V: Clone>(formula: &Formula<V>) -> Vec<Formula<V>> {
    match formula {
        Formula::And(fs) => fs.iter().flat_map(conjuncts).collect(),
        f if f.is_top() => Vec::new(),
        f => vec![f.clone()],
    }
}

/// A variable of a contract conjunct that an instance fixes: a free variable of the contract, or
/// a variable bound by the conjunct's outermost `exists`, skolemised at a head term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Slot<V> {
    Free(V),
    Bound(String),
}

/// The instances of a contract conjunct at the head terms, at most `limit` of them.
///
/// Every free variable is replaced by a head term of its sort (`var_sort`; a variable with no
/// sort gives no instance). An outermost `exists` is kept as written and also opened: each
/// conjunct of its body is instantiated with the bound variables as further slots.
pub fn instances<V>(
    conjunct: &Formula<V>,
    var_sort: &dyn Fn(&V) -> Option<Sort>,
    head: &HeadTerms,
    limit: usize,
) -> Vec<Formula>
where
    V: Clone + Eq + Hash,
{
    let mut out = instances_with(conjunct, &[], var_sort, head, limit);
    if let Formula::Exists(vars, body) = conjunct {
        for inner in conjuncts(body) {
            out.extend(instances_with(&inner, vars, var_sort, head, limit));
        }
    }
    out
}

fn instances_with<V>(
    conjunct: &Formula<V>,
    bound: &[(String, Sort)],
    var_sort: &dyn Fn(&V) -> Option<Sort>,
    head: &HeadTerms,
    limit: usize,
) -> Vec<Formula>
where
    V: Clone + Eq + Hash,
{
    if conjunct
        .iter_atoms()
        .any(|a| matches!(a.pred, Pred::Var(_)))
    {
        return Vec::new();
    }
    let mut slots: Vec<(Slot<V>, Sort)> = Vec::new();
    for v in conjunct.fv() {
        let Some(sort) = var_sort(v) else {
            return Vec::new();
        };
        let slot = Slot::Free(v.clone());
        if !slots.iter().any(|(s, _)| *s == slot) {
            slots.push((slot, sort));
        }
    }
    for (name, sort) in bound {
        slots.push((Slot::Bound(name.clone()), sort.clone()));
    }
    let fillers: Vec<Vec<Term>> = slots.iter().map(|(_, s)| head.fillers(s)).collect();
    if fillers.iter().any(Vec::is_empty) {
        return Vec::new();
    }

    let mut out = Vec::new();
    let mut choice = vec![0; slots.len()];
    loop {
        if out.len() >= limit {
            break;
        }
        if distinct(&slots, &fillers, &choice) {
            let assignment: HashMap<Slot<V>, Term> = slots
                .iter()
                .zip(&fillers)
                .zip(&choice)
                .map(|(((slot, _), fs), &i)| (slot.clone(), fs[i].clone()))
                .collect();
            let instance = substitute(conjunct, &assignment);
            if !instance.is_top() {
                out.push(instance);
            }
        }
        if !advance(&mut choice, &fillers) {
            break;
        }
    }
    out
}

/// Whether no two slots of the same sort are given the same term.
fn distinct<V>(slots: &[(Slot<V>, Sort)], fillers: &[Vec<Term>], choice: &[usize]) -> bool {
    for i in 0..slots.len() {
        for j in i + 1..slots.len() {
            if slots[i].1 == slots[j].1 && fillers[i][choice[i]] == fillers[j][choice[j]] {
                return false;
            }
        }
    }
    true
}

fn advance(choice: &mut [usize], fillers: &[Vec<Term>]) -> bool {
    for (c, fs) in choice.iter_mut().zip(fillers) {
        *c += 1;
        if *c < fs.len() {
            return true;
        }
        *c = 0;
    }
    false
}

fn substitute<V>(conjunct: &Formula<V>, assignment: &HashMap<Slot<V>, Term>) -> Formula
where
    V: Clone + Eq + Hash,
{
    let formula = conjunct
        .clone()
        .subst_var(|v| assignment[&Slot::Free(v)].clone());
    let mut formula = map_formula_terms(formula, &mut |t| match t {
        Term::FormulaQuantifiedVar(sort, name) => assignment
            .get(&Slot::Bound(name.clone()))
            .cloned()
            .unwrap_or(Term::FormulaQuantifiedVar(sort, name)),
        t => simplify_term(t),
    });
    formula.simplify();
    formula
}

fn simplify_term(term: Term) -> Term {
    match term {
        Term::MutCurrent(t) => match *t {
            Term::Mut(current, _) => *current,
            t => Term::MutCurrent(Box::new(t)),
        },
        Term::MutFinal(t) => match *t {
            Term::Mut(_, final_) => *final_,
            t => Term::MutFinal(Box::new(t)),
        },
        Term::BoxCurrent(t) => match *t {
            Term::Box(inner) => *inner,
            t => Term::BoxCurrent(Box::new(t)),
        },
        Term::TupleProj(t, i) => match *t {
            Term::Tuple(mut ts) => ts.swap_remove(i),
            t => Term::TupleProj(Box::new(t), i),
        },
        t => t,
    }
}

/// Rewrites every term of `formula` bottom-up with `f`.
fn map_formula_terms(formula: Formula, f: &mut dyn FnMut(Term) -> Term) -> Formula {
    match formula {
        Formula::Atom(atom) => Formula::Atom(map_atom_terms(atom, f)),
        Formula::Not(fo) => Formula::Not(Box::new(map_formula_terms(*fo, f))),
        Formula::And(fs) => {
            Formula::And(fs.into_iter().map(|fo| map_formula_terms(fo, f)).collect())
        }
        Formula::Or(fs) => Formula::Or(fs.into_iter().map(|fo| map_formula_terms(fo, f)).collect()),
        Formula::Implies(lhs, rhs) => Formula::Implies(
            Box::new(map_formula_terms(*lhs, f)),
            Box::new(map_formula_terms(*rhs, f)),
        ),
        Formula::Exists(vars, fo) => Formula::Exists(vars, Box::new(map_formula_terms(*fo, f))),
        Formula::Forall(vars, fo) => Formula::Forall(vars, Box::new(map_formula_terms(*fo, f))),
    }
}

fn map_atom_terms(atom: Atom, f: &mut dyn FnMut(Term) -> Term) -> Atom {
    let Atom { guard, pred, args } = atom;
    Atom {
        guard: guard.map(|g| Box::new(map_formula_terms(*g, f))),
        pred,
        args: args.into_iter().map(|t| map_term(t, f)).collect(),
    }
}

fn map_term(term: Term, f: &mut dyn FnMut(Term) -> Term) -> Term {
    let sub = |t: Box<Term>, f: &mut dyn FnMut(Term) -> Term| Box::new(map_term(*t, f));
    let term = match term {
        Term::Box(t) => Term::Box(sub(t, f)),
        Term::Mut(t1, t2) => {
            let t1 = sub(t1, f);
            Term::Mut(t1, sub(t2, f))
        }
        Term::BoxCurrent(t) => Term::BoxCurrent(sub(t, f)),
        Term::MutCurrent(t) => Term::MutCurrent(sub(t, f)),
        Term::MutFinal(t) => Term::MutFinal(sub(t, f)),
        Term::App(fun, args) => Term::App(fun, args.into_iter().map(|t| map_term(t, f)).collect()),
        Term::Tuple(ts) => Term::Tuple(ts.into_iter().map(|t| map_term(t, f)).collect()),
        Term::TupleProj(t, i) => Term::TupleProj(sub(t, f), i),
        Term::DatatypeCtor(sort, sym, args) => Term::DatatypeCtor(
            sort,
            sym,
            args.into_iter().map(|t| map_term(t, f)).collect(),
        ),
        Term::DatatypeDiscr(sym, t) => Term::DatatypeDiscr(sym, sub(t, f)),
        Term::UserDefinedFn(sym, sort, args) => Term::UserDefinedFn(
            sym,
            sort,
            args.into_iter().map(|t| map_term(t, f)).collect(),
        ),
        t @ (Term::Null
        | Term::ForallDefault(_)
        | Term::Var(_)
        | Term::Bool(_)
        | Term::Int(_)
        | Term::String(_)
        | Term::ArrayEmpty(_, _)
        | Term::SeqEmpty(_)
        | Term::FormulaQuantifiedVar(_, _)) => t,
    };
    f(term)
}

/// The forall predicates `atom` names, directly or through a user-defined predicate.
pub(super) fn forall_preds_of<'a>(
    formula: &'a Formula,
    user_defined: &'a [UserDefinedPredDef],
) -> Vec<&'a ForallPred> {
    let mut preds = Vec::new();
    for atom in formula.iter_atoms() {
        match &atom.pred {
            Pred::ForallPred(p) => preds.push(p),
            Pred::UserDefined(sym) => {
                for def in user_defined.iter().filter(|d| &d.symbol == sym) {
                    preds.extend(def.dependencies.iter());
                }
            }
            _ => {}
        }
    }
    preds
}
