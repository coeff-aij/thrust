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
            if !is_trivial(&instance) {
                out.push(instance);
            }
        }
        if !advance(&mut choice, &fillers) {
            break;
        }
    }
    out
}

/// Whether `formula` holds whatever its variables are, by its shape: `true`, `t = t`,
/// `t <= t`, `t >= t`, or `A => A`. Such an instance comes from a reference whose current and
/// final values were given the same term.
fn is_trivial(formula: &Formula) -> bool {
    match formula {
        Formula::Atom(atom) => {
            let reflexive = [
                KnownPred::EQUAL,
                KnownPred::LESS_THAN_OR_EQUAL,
                KnownPred::GREATER_THAN_OR_EQUAL,
            ];
            atom.is_top()
                || (atom.guard.is_none()
                    && atom.args.len() == 2
                    && atom.args[0] == atom.args[1]
                    && reflexive.iter().any(|&p| atom.pred == Pred::Known(p)))
        }
        Formula::Implies(lhs, rhs) => lhs == rhs,
        f => f.is_top(),
    }
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

/// Which candidate atoms loop heads get: `THRUST_CANDIDATE_ATOMS=1` from contracts,
/// `THRUST_CANDIDATE_ATOMS=2` also from the facts that hold where the loop is entered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CandidateAtomsMode {
    Off,
    Contracts,
    ContractsAndEntry,
}

impl CandidateAtomsMode {
    pub fn from_env() -> Self {
        match std::env::var("THRUST_CANDIDATE_ATOMS").as_deref() {
            Ok("1") => CandidateAtomsMode::Contracts,
            Ok("2") => CandidateAtomsMode::ContractsAndEntry,
            _ => CandidateAtomsMode::Off,
        }
    }
}

impl System {
    /// Adds to each declared predicate variable the atoms of its entry clauses
    /// ([`entry_atoms`]). Run on the unboxed system.
    pub fn add_entry_candidate_atoms(&mut self) {
        let mut added = Vec::new();
        for candidates in &self.candidate_atoms {
            added.push(entry_atoms(self, candidates.pred));
        }
        for (candidates, atoms) in self.candidate_atoms.iter_mut().zip(added) {
            candidates.atoms.extend(atoms);
        }
    }
}

/// The facts of the clauses that enter `pred` from outside (its head is `pred`, its body does not
/// apply it), over `pred`'s arguments: liquid-fixpoint's scraping of the concrete predicates of a
/// constraint's environment, restricted to where the loop is entered and mapped onto the head
/// instead of abstracted into a qualifier.
///
/// The equalities of the body that define a variable are substituted away, the head's arguments
/// are then read back as terms over the argument positions (`cur`, `final` and tuple fields), and
/// what the head's arguments were built from becomes an equality (`s.n = 0` from an assignment
/// before the loop, `n = e.n`). Every body conjunct over mapped variables is kept, and an integer
/// equality also gives its two inequalities, so that a check that drops `n = e.n` can keep
/// `n <= e.n`.
pub(super) fn entry_atoms(system: &System, pred: PredVarId) -> Vec<Formula> {
    let sig = &system.pred_vars[pred].sig;
    let mut out = Vec::new();
    for clause in &system.clauses {
        if clause.head.pred != Pred::Var(pred)
            || clause.body.atoms.iter().any(|a| a.pred == Pred::Var(pred))
        {
            continue;
        }
        for atom in entry_atoms_of(system, clause) {
            let split = int_equality_halves(&atom, sig);
            out.push(atom);
            out.extend(split);
        }
    }
    out.retain(|atom| !is_trivial(atom));
    out
}

/// How many levels of single-clause predicate variables [`clause_facts`] unfolds.
const UNFOLD_DEPTH: usize = 3;

fn entry_atoms_of(system: &System, clause: &Clause) -> Vec<Formula> {
    let mut next_var = clause.vars.len();
    let facts = clause_facts(system, clause, 0, &mut next_var, UNFOLD_DEPTH);
    let head = clause.head.args.clone();
    entry_atoms_from(facts, head)
}

/// The concrete facts of `clause`'s body (and head guard), its variables shifted by `offset`.
/// A predicate variable of the body that has exactly one defining clause, not recursive, is
/// unfolded into that clause's facts, with fresh variables from `next_var`, down to `depth`
/// levels (liquid-fixpoint's elimination of a variable with a single definition): the facts
/// that reach a loop through the block before it are otherwise hidden in that block's unknown.
fn clause_facts(
    system: &System,
    clause: &Clause,
    offset: usize,
    next_var: &mut usize,
    depth: usize,
) -> Vec<Formula> {
    let shift = |v: TermVarIdx| Term::var(TermVarIdx::from_usize(v.index() + offset));
    let mut facts: Vec<Formula> = conjuncts(&clause.body.formula)
        .into_iter()
        .chain(clause.head.guard.iter().flat_map(|g| conjuncts(g)))
        .map(|f| f.subst_var(shift))
        .collect();
    for atom in &clause.body.atoms {
        let atom = atom.clone().subst_var(shift);
        let Pred::Var(q) = atom.pred else {
            facts.push(Formula::Atom(atom));
            continue;
        };
        if depth == 0 {
            continue;
        }
        let Some(def) = single_definition(system, q) else {
            continue;
        };
        let def_offset = *next_var;
        *next_var += def.vars.len();
        let def_shift = |v: TermVarIdx| Term::var(TermVarIdx::from_usize(v.index() + def_offset));
        for (arg, param) in atom.args.iter().zip(&def.head.args) {
            let param = param.clone().subst_var(def_shift);
            facts.push(Formula::Atom(arg.clone().equal_to(param)));
        }
        facts.extend(clause_facts(system, def, def_offset, next_var, depth - 1));
    }
    facts
}

/// The only clause whose head is `pred`, if there is one and its body does not apply `pred`.
fn single_definition(system: &System, pred: PredVarId) -> Option<&Clause> {
    let mut defs = system
        .clauses
        .iter()
        .filter(|c| c.head.pred == Pred::Var(pred));
    let def = defs.next()?;
    if defs.next().is_some() || def.body.atoms.iter().any(|a| a.pred == Pred::Var(pred)) {
        return None;
    }
    Some(def)
}

fn entry_atoms_from(mut facts: Vec<Formula>, mut head: Vec<Term>) -> Vec<Formula> {
    while let Some((x, t)) = take_definition(&mut facts) {
        let subst = |v: TermVarIdx| if v == x { t.clone() } else { Term::Var(v) };
        facts = facts
            .into_iter()
            .map(|f| map_formula_terms(f.subst_var(subst), &mut simplify_term))
            .collect();
        head = head
            .into_iter()
            .map(|h| map_term(h.subst_var(subst), &mut simplify_term))
            .collect();
    }

    let mut mapping: HashMap<TermVarIdx, Term> = HashMap::new();
    let mut built = Vec::new();
    for (k, h) in head.into_iter().enumerate() {
        read_back(
            h,
            Term::var(TermVarIdx::from_usize(k)),
            &mut mapping,
            &mut built,
        );
    }
    let mapped = |f: &Formula| f.fv().all(|v| mapping.contains_key(v));
    let mut out = Vec::new();
    for (at, h) in built {
        if h.fv().all(|v| mapping.contains_key(v)) {
            let h = h.subst_var(|v| mapping[&v].clone());
            out.push(Formula::Atom(at.equal_to(h)));
        }
    }
    for fact in facts.iter().filter(|f| mapped(f)) {
        let fact = fact.clone().subst_var(|v| mapping[&v].clone());
        out.push(map_formula_terms(fact, &mut simplify_term));
    }
    out
}

/// Removes from `facts` an equality that defines a variable, `x = t` with `x` not in `t`, and
/// returns it; an equality of two references or tuples is split into its components first.
fn take_definition(facts: &mut Vec<Formula>) -> Option<(TermVarIdx, Term)> {
    loop {
        let i = facts.iter().position(|f| equality_sides(f).is_some())?;
        let (lhs, rhs) = equality_sides(&facts[i]).unwrap();
        let (lhs, rhs) = (lhs.clone(), rhs.clone());
        match (lhs, rhs) {
            (Term::Mut(a, b), Term::Mut(c, d)) => {
                facts[i] = Formula::Atom(a.equal_to(*c));
                facts.push(Formula::Atom(b.equal_to(*d)));
            }
            (Term::Tuple(xs), Term::Tuple(ys)) if xs.len() == ys.len() => {
                facts.remove(i);
                facts.extend(
                    xs.into_iter()
                        .zip(ys)
                        .map(|(x, y)| Formula::Atom(x.equal_to(y))),
                );
            }
            (Term::Var(x), t) | (t, Term::Var(x)) if !t.fv().any(|v| *v == x) => {
                facts.remove(i);
                return Some((x, t));
            }
            _ => return definition_elsewhere(facts, i),
        }
    }
}

/// [`take_definition`] past the equality at `skip`, which defines no variable.
fn definition_elsewhere(facts: &mut Vec<Formula>, skip: usize) -> Option<(TermVarIdx, Term)> {
    let mut rest = facts.split_off(skip + 1);
    let found = take_definition(&mut rest);
    facts.extend(rest);
    found
}

fn equality_sides(f: &Formula) -> Option<(&Term, &Term)> {
    let Formula::Atom(atom) = f else {
        return None;
    };
    if atom.guard.is_some() || atom.pred != Pred::Known(KnownPred::EQUAL) || atom.args.len() != 2 {
        return None;
    }
    Some((&atom.args[0], &atom.args[1]))
}

/// Reads the head argument `h` as the term `at` over the argument positions: a variable is
/// mapped to `at` (or, if already mapped, gives an equality), a reference or tuple is read
/// component-wise, and anything else is an equality `at = h` to state once its variables are
/// mapped.
fn read_back(
    h: Term,
    at: Term,
    mapping: &mut HashMap<TermVarIdx, Term>,
    built: &mut Vec<(Term, Term)>,
) {
    match h {
        Term::Var(x) if !mapping.contains_key(&x) => {
            mapping.insert(x, at);
        }
        Term::Mut(current, final_) => {
            read_back(*current, at.clone().mut_current(), mapping, built);
            read_back(*final_, at.mut_final(), mapping, built);
        }
        Term::Tuple(ts) => {
            for (i, t) in ts.into_iter().enumerate() {
                read_back(t, at.clone().tuple_proj(i), mapping, built);
            }
        }
        h => built.push((at, h)),
    }
}

/// `a <= b` and `a >= b` for an integer equality `a = b` over the arguments of sorts `sig`.
fn int_equality_halves(atom: &Formula, sig: &[Sort]) -> Vec<Formula> {
    let Some((a, b)) = equality_sides(atom) else {
        return Vec::new();
    };
    if a.sort(|v| sig[v.index()].clone()) != Sort::Int {
        return Vec::new();
    }
    [
        KnownPred::LESS_THAN_OR_EQUAL,
        KnownPred::GREATER_THAN_OR_EQUAL,
    ]
    .into_iter()
    .map(|p| Formula::Atom(Atom::new(p.into(), vec![a.clone(), b.clone()])))
    .collect()
}
