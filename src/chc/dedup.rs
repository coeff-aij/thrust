//! An optimization that removes predicate variable arguments that are inductively equal to
//! another argument of the same predicate variable.
//!
//! A column `j` of a predicate variable `P` is removed when there is a column `i < j` of the
//! same sort such that every clause with `P` in its head establishes `a_i = a_j` for the head's
//! arguments, from the equalities among the top-level conjuncts of its body and from the same
//! property of the predicate variables in its body (assumed inductively and checked to a
//! fixpoint). The check runs over leaf components rather than columns: the projections a
//! flattening would split a tuple, `Box` or `Mut` argument into, so that an equality between a
//! component of one argument and a component of another (a loop body's `&mut Vec` and its
//! iterator's entry sequence) carries through a predicate whose arguments are not flattened.
//! Only a pair of two whole columns removes a column. The column is dropped from the signature and from every atom of `P`, and each
//! body atom `P(a)` leaves the equality `a_i = a_j` behind as a conjunct of the body (under the
//! atom's guard, if it has one), so that the new body is the old one with
//! `P(x) := P'(x without j) ∧ x_i = x_j`. With that definition a solution of the reduced system
//! is a solution of the original one, since every head clause establishes `a_i = a_j`; and a
//! solution of the original one, conjoined with `x_i = x_j` (still a solution by the same
//! check), gives one of the reduced system. Without the equality left behind the reduction would
//! lose solutions: a goal clause `P(x, y) ∧ x ≠ y ⇒ ⊥` would become `P'(x) ∧ x ≠ y ⇒ ⊥`.
//!
//! Equality inside a clause is decided by a congruence closure over the terms of its top-level
//! equalities and predicate variable arguments, which also knows that a projection of a
//! constructed tuple or mutable reference is the corresponding component and that constructors
//! are injective. An equality under a top-level disjunction is used when every disjunct
//! establishes it; nothing is derived from negations, implications or nested disjunctions.

use std::collections::{HashMap, HashSet};

use super::*;

/// The symbol of a compound term, with its arguments left out.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Op {
    Box,
    Mut,
    BoxCurrent,
    MutCurrent,
    MutFinal,
    App(Function),
    Tuple,
    TupleProj(usize),
    Ctor(DatatypeSort, DatatypeSymbol),
    Discr(DatatypeSymbol),
}

impl Op {
    /// Whether the operator is a constructor, so that equal applications have equal arguments.
    fn is_injective(&self) -> bool {
        matches!(self, Op::Box | Op::Mut | Op::Tuple | Op::Ctor(..))
    }
}

/// The operator and the arguments of a compound term; `None` for a leaf.
fn decompose(term: &Term) -> Option<(Op, Vec<&Term>)> {
    let decomposed = match term {
        Term::Var(_)
        | Term::Bool(_)
        | Term::Int(_)
        | Term::String(_)
        | Term::Null
        | Term::ForallDefault(_)
        | Term::ArrayEmpty(..)
        | Term::SeqEmpty(_)
        | Term::FormulaQuantifiedVar(..) => return None,
        Term::Box(t) => (Op::Box, vec![&**t]),
        Term::Mut(t1, t2) => (Op::Mut, vec![&**t1, &**t2]),
        Term::BoxCurrent(t) => (Op::BoxCurrent, vec![&**t]),
        Term::MutCurrent(t) => (Op::MutCurrent, vec![&**t]),
        Term::MutFinal(t) => (Op::MutFinal, vec![&**t]),
        Term::App(fun, args) => (Op::App(*fun), args.iter().collect()),
        Term::Tuple(ts) => (Op::Tuple, ts.iter().collect()),
        Term::TupleProj(t, i) => (Op::TupleProj(*i), vec![&**t]),
        Term::DatatypeCtor(sort, sym, args) => {
            (Op::Ctor(sort.clone(), sym.clone()), args.iter().collect())
        }
        Term::DatatypeDiscr(sym, t) => (Op::Discr(sym.clone()), vec![&**t]),
    };
    Some(decomposed)
}

/// The component a projection operator selects from a constructor, if it selects one.
fn projected_component(proj: &Op, ctor: &Op) -> Option<usize> {
    match (proj, ctor) {
        (Op::TupleProj(i), Op::Tuple) => Some(*i),
        (Op::MutCurrent, Op::Mut) | (Op::BoxCurrent, Op::Box) => Some(0),
        (Op::MutFinal, Op::Mut) => Some(1),
        _ => None,
    }
}

#[derive(Debug, Clone)]
struct Node {
    op: Option<Op>,
    children: Vec<usize>,
}

/// A congruence closure over the terms of one clause.
#[derive(Debug, Clone, Default)]
struct Congruence {
    ids: HashMap<Term, usize>,
    nodes: Vec<Node>,
    parent: Vec<usize>,
}

impl Congruence {
    fn intern(&mut self, term: &Term) -> usize {
        if let Some(&id) = self.ids.get(term) {
            return id;
        }
        let node = match decompose(term) {
            None => Node {
                op: None,
                children: Vec::new(),
            },
            Some((op, args)) => Node {
                op: Some(op),
                children: args.into_iter().map(|t| self.intern(t)).collect(),
            },
        };
        let id = self.nodes.len();
        self.nodes.push(node);
        self.parent.push(id);
        self.ids.insert(term.clone(), id);
        id
    }

    fn find(&mut self, mut id: usize) -> usize {
        while self.parent[id] != id {
            self.parent[id] = self.parent[self.parent[id]];
            id = self.parent[id];
        }
        id
    }

    /// Returns whether the two classes were distinct.
    fn union(&mut self, a: usize, b: usize) -> bool {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return false;
        }
        self.parent[a.max(b)] = a.min(b);
        true
    }

    fn union_terms(&mut self, t1: &Term, t2: &Term) {
        let (a, b) = (self.intern(t1), self.intern(t2));
        self.union(a, b);
    }

    /// Whether the two terms are equal. A term not seen before is interned and the closure run
    /// again, so that a projection of a constructed value meets its component.
    fn equal(&mut self, t1: &Term, t2: &Term) -> bool {
        let known = self.nodes.len();
        let (a, b) = (self.intern(t1), self.intern(t2));
        if self.nodes.len() > known {
            self.close();
        }
        self.find(a) == self.find(b)
    }

    /// Merges congruent applications, the arguments of equal constructors, and projections of
    /// constructors with the projected component, until nothing changes.
    fn close(&mut self) {
        while self.close_once() {}
    }

    fn close_once(&mut self) -> bool {
        let mut changed = false;
        let mut signatures: HashMap<(Op, Vec<usize>), usize> = HashMap::new();
        let mut ctors: HashMap<usize, Vec<usize>> = HashMap::new();
        for id in 0..self.nodes.len() {
            let Some(op) = self.nodes[id].op.clone() else {
                continue;
            };
            let children: Vec<usize> = (0..self.nodes[id].children.len())
                .map(|k| self.find(self.nodes[id].children[k]))
                .collect();
            if op.is_injective() {
                let class = self.find(id);
                ctors.entry(class).or_default().push(id);
            }
            match signatures.get(&(op.clone(), children.clone())) {
                Some(&other) => changed |= self.union(id, other),
                None => {
                    signatures.insert((op, children), id);
                }
            }
        }
        for members in ctors.values() {
            for pair in members.windows(2) {
                changed |= self.merge_constructor_args(pair[0], pair[1]);
            }
        }
        for id in 0..self.nodes.len() {
            changed |= self.project(id, &ctors);
        }
        changed
    }

    fn merge_constructor_args(&mut self, a: usize, b: usize) -> bool {
        if self.nodes[a].op != self.nodes[b].op {
            return false;
        }
        let pairs: Vec<(usize, usize)> = self.nodes[a]
            .children
            .iter()
            .copied()
            .zip(self.nodes[b].children.iter().copied())
            .collect();
        let mut changed = false;
        for (x, y) in pairs {
            changed |= self.union(x, y);
        }
        changed
    }

    fn project(&mut self, id: usize, ctors: &HashMap<usize, Vec<usize>>) -> bool {
        let Some(proj) = self.nodes[id].op.clone() else {
            return false;
        };
        let Some(&target) = self.nodes[id].children.first() else {
            return false;
        };
        let class = self.find(target);
        let Some(members) = ctors.get(&class) else {
            return false;
        };
        let mut changed = false;
        for &ctor in members {
            let Some(ctor_op) = &self.nodes[ctor].op else {
                continue;
            };
            let Some(k) = projected_component(&proj, ctor_op) else {
                continue;
            };
            if let Some(&component) = self.nodes[ctor].children.get(k) {
                changed |= self.union(id, component);
            }
        }
        changed
    }
}

/// One step of a projection path into an argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Step {
    Proj(usize),
    Current,
    Final,
    BoxCurrent,
}

/// A leaf component of a predicate variable's arguments: the projection `path` of argument
/// `column`, split the way flattening splits a tuple, `Box` or `Mut` argument. When no argument
/// is composite, the leaves are the columns.
#[derive(Debug, Clone)]
struct Leaf {
    column: usize,
    path: Vec<Step>,
    sort: Sort,
}

impl Leaf {
    fn term(&self, args: &[Term]) -> Term {
        let mut term = args[self.column].clone();
        for step in &self.path {
            term = match step {
                Step::Proj(i) => Term::TupleProj(Box::new(term), *i),
                Step::Current => Term::MutCurrent(Box::new(term)),
                Step::Final => Term::MutFinal(Box::new(term)),
                Step::BoxCurrent => Term::BoxCurrent(Box::new(term)),
            };
        }
        term
    }

    fn is_column(&self) -> bool {
        self.path.is_empty()
    }
}

fn push_leaves(out: &mut Vec<Leaf>, column: usize, path: Vec<Step>, sort: &Sort) {
    let mut sub = |step: Step, sort: &Sort| {
        let mut path = path.clone();
        path.push(step);
        push_leaves(out, column, path, sort);
    };
    match sort {
        Sort::Tuple(sorts) => {
            for (i, s) in sorts.iter().enumerate() {
                if !s.is_singleton() {
                    sub(Step::Proj(i), s);
                }
            }
        }
        Sort::Box(inner) => sub(Step::BoxCurrent, inner),
        Sort::Mut(inner) => {
            sub(Step::Current, inner);
            sub(Step::Final, inner);
        }
        _ => out.push(Leaf {
            column,
            path,
            sort: sort.clone(),
        }),
    }
}

fn leaves_of(sig: &PredSig) -> Vec<Leaf> {
    let mut out = Vec::new();
    for (column, sort) in sig.iter().enumerate() {
        push_leaves(&mut out, column, Vec::new(), sort);
    }
    out
}

/// The leaves of each predicate variable, and the alive pairs `(a, b)`, `a < b`, of leaf indices.
#[derive(Debug, Default)]
struct Pairs {
    leaves: HashMap<PredVarId, Vec<Leaf>>,
    alive: HashMap<PredVarId, Vec<(usize, usize)>>,
}

impl Pairs {
    /// The pairs of `atom`'s predicate variable as pairs of argument terms.
    fn terms<'a>(&'a self, atom: &'a Atom) -> impl Iterator<Item = (Term, Term)> + 'a {
        let (leaves, pairs) = match atom.pred {
            Pred::Var(p) => (self.leaves.get(&p), self.alive.get(&p)),
            _ => (None, None),
        };
        pairs.into_iter().flatten().map(move |&(a, b)| {
            let leaves = leaves.expect("leaves of a predicate with pairs");
            (leaves[a].term(&atom.args), leaves[b].term(&atom.args))
        })
    }
}

fn equality_args<V>(atom: &Atom<V>) -> Option<(&Term<V>, &Term<V>)> {
    if atom.guard.is_some() || atom.pred != Pred::Known(KnownPred::EQUAL) {
        return None;
    }
    match atom.args.as_slice() {
        [t1, t2] => Some((t1, t2)),
        _ => None,
    }
}

/// The equalities among the top-level conjuncts of a formula, and its top-level disjunctions.
#[derive(Default)]
struct Conjuncts<'a> {
    equalities: Vec<(&'a Term, &'a Term)>,
    disjunctions: Vec<&'a [Formula]>,
}

impl<'a> Conjuncts<'a> {
    fn push(&mut self, formula: &'a Formula) {
        match formula {
            Formula::And(fs) => {
                for f in fs {
                    self.push(f);
                }
            }
            Formula::Or(fs) => self.disjunctions.push(fs),
            Formula::Atom(atom) => self.equalities.extend(equality_args(atom)),
            _ => {}
        }
    }
}

/// What a clause body establishes about equality: its congruence closure, and for each
/// top-level disjunction the closure under each disjunct. An equality holds when the closure
/// has it or when every disjunct of one disjunction does (a one-level case split).
struct BodyEqualities {
    base: Congruence,
    cases: Vec<Vec<Congruence>>,
}

impl BodyEqualities {
    fn equal(&mut self, t1: &Term, t2: &Term) -> bool {
        if self.base.equal(t1, t2) {
            return true;
        }
        self.cases
            .iter_mut()
            .any(|disjuncts| disjuncts.iter_mut().all(|cc| cc.equal(t1, t2)))
    }
}

fn case_congruence(base: &Congruence, disjunct: &Formula) -> Congruence {
    let mut cc = base.clone();
    let mut conjuncts = Conjuncts::default();
    conjuncts.push(disjunct);
    for (t1, t2) in conjuncts.equalities {
        cc.union_terms(t1, t2);
    }
    cc.close();
    cc
}

/// The equalities a clause body establishes under the inductive assumption `alive`.
fn body_equalities(clause: &Clause, alive: &Pairs) -> BodyEqualities {
    let mut cc = Congruence::default();
    let mut conjuncts = Conjuncts::default();
    conjuncts.push(&clause.body.formula);
    conjuncts
        .equalities
        .extend(clause.body.atoms.iter().filter_map(equality_args));
    for &(t1, t2) in &conjuncts.equalities {
        cc.union_terms(t1, t2);
    }
    for atom in &clause.body.atoms {
        if atom.guard.is_some() {
            continue;
        }
        for (t1, t2) in alive.terms(atom) {
            cc.union_terms(&t1, &t2);
        }
    }
    for atom in &clause.head_and_body_atoms() {
        for arg in &atom.args {
            cc.intern(arg);
        }
    }
    cc.close();
    let cases = conjuncts
        .disjunctions
        .iter()
        .map(|disjuncts| disjuncts.iter().map(|d| case_congruence(&cc, d)).collect())
        .collect();
    BodyEqualities { base: cc, cases }
}

impl Clause {
    fn head_and_body_atoms(&self) -> Vec<&Atom> {
        std::iter::once(&self.head)
            .chain(self.body.atoms.iter())
            .filter(|atom| matches!(atom.pred, Pred::Var(_)))
            .collect()
    }
}

/// Removes the pairs of the head predicate variable of `clause` that its body does not
/// establish. Returns whether a pair was removed.
fn kill_unestablished(clause: &Clause, alive: &mut Pairs) -> bool {
    let Pred::Var(p) = clause.head.pred else {
        return false;
    };
    let Some(pairs) = alive.alive.get(&p) else {
        return false;
    };
    if pairs.is_empty() {
        return false;
    }
    let mut equalities = body_equalities(clause, alive);
    let leaves = &alive.leaves[&p];
    let args = &clause.head.args;
    let pairs = pairs.clone();
    let kept: Vec<_> = pairs
        .iter()
        .copied()
        .filter(|&(a, b)| equalities.equal(&leaves[a].term(args), &leaves[b].term(args)))
        .collect();
    let killed = kept.len() != pairs.len();
    if killed {
        tracing::debug!(pred = %p, ?pairs, ?kept, clause = %clause.display(), "dedup_pred_args: killed pairs");
    }
    alive.alive.insert(p, kept);
    killed
}

fn collect_pred_vars(formula: &Formula, out: &mut HashSet<PredVarId>) {
    for atom in formula.iter_atoms() {
        collect_atom_pred_vars(atom, out);
    }
}

fn collect_atom_pred_vars(atom: &Atom, out: &mut HashSet<PredVarId>) {
    if let Pred::Var(p) = atom.pred {
        out.insert(p);
    }
    if let Some(guard) = &atom.guard {
        collect_pred_vars(guard, out);
    }
}

/// Predicate variables that occur somewhere other than as a clause head or a body atom: in a
/// formula, a guard, the body of a user-defined predicate or a law. The pass leaves them alone,
/// since it only rewrites heads and body atoms.
pub(super) fn pred_vars_in_formulas(system: &System) -> HashSet<PredVarId> {
    let mut out = HashSet::new();
    for clause in &system.clauses {
        collect_pred_vars(&clause.body.formula, &mut out);
        for atom in std::iter::once(&clause.head).chain(&clause.body.atoms) {
            if let Some(guard) = &atom.guard {
                collect_pred_vars(guard, &mut out);
            }
        }
    }
    for def in &system.user_defined_pred_defs {
        if let UserDefinedPredBody::Formula(formula) = &def.body {
            collect_pred_vars(formula, &mut out);
        }
    }
    for laws in system.laws.values() {
        for law in laws {
            collect_pred_vars(law, &mut out);
        }
    }
    out
}

fn candidate_pairs(system: &System) -> Pairs {
    let excluded = pred_vars_in_formulas(system);
    let mut pairs = Pairs::default();
    for (p, def) in system.pred_vars.iter_enumerated() {
        if excluded.contains(&p) {
            continue;
        }
        let leaves = leaves_of(&def.sig);
        let candidates = (0..leaves.len())
            .flat_map(|a| (a + 1..leaves.len()).map(move |b| (a, b)))
            .filter(|&(a, b)| leaves[a].sort == leaves[b].sort)
            .collect();
        pairs.leaves.insert(p, leaves);
        pairs.alive.insert(p, candidates);
    }
    pairs
}

/// The inductively established pairs of every predicate variable.
fn established_pairs(system: &System) -> Pairs {
    let mut alive = candidate_pairs(system);
    loop {
        let mut killed = false;
        for clause in &system.clauses {
            killed |= kill_unestablished(clause, &mut alive);
        }
        if !killed {
            return alive;
        }
    }
}

/// The columns to drop for each predicate variable, each with the lowest column an established
/// pair relates it to. Only a pair of two whole columns lets a column go.
fn dropped_columns(pairs: &Pairs) -> HashMap<PredVarId, BTreeMap<usize, usize>> {
    let mut dropped: HashMap<PredVarId, BTreeMap<usize, usize>> = HashMap::new();
    for (p, alive) in &pairs.alive {
        let leaves = &pairs.leaves[p];
        for &(a, b) in alive {
            let (i, j) = (&leaves[a], &leaves[b]);
            if !i.is_column() || !j.is_column() {
                continue;
            }
            let rep = dropped
                .entry(*p)
                .or_default()
                .entry(j.column)
                .or_insert(i.column);
            *rep = (*rep).min(i.column);
        }
    }
    dropped
}

fn keep_columns<T>(items: Vec<T>, dropped: &BTreeMap<usize, usize>) -> Vec<T> {
    items
        .into_iter()
        .enumerate()
        .filter(|(k, _)| !dropped.contains_key(k))
        .map(|(_, t)| t)
        .collect()
}

/// The equalities `a_i = a_j` a body atom stands for with its column `j` dropped, under the
/// atom's guard if it has one.
fn dropped_equalities(atom: &Atom, dropped: &BTreeMap<usize, usize>) -> Vec<Formula> {
    dropped
        .iter()
        .map(|(&j, &i)| {
            let eq = Formula::Atom(atom.args[i].clone().equal_to(atom.args[j].clone()));
            match &atom.guard {
                None => eq,
                Some(guard) => Formula::Implies(guard.clone(), Box::new(eq)),
            }
        })
        .collect()
}

fn drop_in_clause(clause: &mut Clause, dropped: &HashMap<PredVarId, BTreeMap<usize, usize>>) {
    let columns_of = |atom: &Atom| match atom.pred {
        Pred::Var(p) => dropped.get(&p),
        _ => None,
    };
    let mut equalities = Vec::new();
    for atom in &mut clause.body.atoms {
        let Some(columns) = columns_of(atom) else {
            continue;
        };
        equalities.extend(dropped_equalities(atom, columns));
        atom.args = keep_columns(std::mem::take(&mut atom.args), columns);
    }
    for eq in equalities {
        clause.body.formula.push_conj(eq);
    }
    if let Some(columns) = columns_of(&clause.head) {
        clause.head.args = keep_columns(std::mem::take(&mut clause.head.args), columns);
    }
}

/// The predicate variables that occur both in the head and in the body of one clause: at the CHC
/// level, the loop heads.
pub(super) fn recursive_pred_vars(system: &System) -> HashSet<PredVarId> {
    system
        .clauses
        .iter()
        .filter_map(|clause| match clause.head.pred {
            Pred::Var(p) if clause.body.atoms.iter().any(|a| a.pred == Pred::Var(p)) => Some(p),
            _ => None,
        })
        .collect()
}

/// Removes every predicate variable argument that is inductively equal to a lower argument of
/// the same predicate variable (see the module documentation).
pub fn dedup_pred_args(system: System) -> System {
    dedup_pred_args_where(system, |_| true)
}

/// [`dedup_pred_args`] restricted to the recursive predicate variables (the loop heads). The
/// equalities are still established over every predicate variable, since a loop head's
/// recursive clause usually passes through the predicate of the loop body.
pub fn dedup_recursive_pred_args(system: System) -> System {
    let recursive = recursive_pred_vars(&system);
    dedup_pred_args_where(system, |p| recursive.contains(&p))
}

fn dedup_pred_args_where(mut system: System, drop_at: impl Fn(PredVarId) -> bool) -> System {
    let mut alive = established_pairs(&system);
    alive.alive.retain(|p, _| drop_at(*p));
    tracing::debug!(?alive, "dedup_pred_args: established pairs");
    let dropped = dropped_columns(&alive);
    let mut preds: Vec<_> = dropped.keys().copied().collect();
    preds.sort_by_key(|p| p.index());
    for p in preds {
        let columns = &dropped[&p];
        tracing::info!(pred = %p, ?columns, sig_len = system.pred_vars[p].sig.len(), "dedup_pred_args: dropping columns");
        let sig = std::mem::take(&mut system.pred_vars[p].sig);
        system.pred_vars[p].sig = keep_columns(sig, columns);
    }
    for clause in system.clauses.iter_mut() {
        drop_in_clause(clause, &dropped);
    }
    system
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(vars: Vec<Sort>, head: Atom, body: Body) -> Clause {
        let sort = vars.first().cloned().unwrap_or_else(Sort::int);
        Clause {
            origin: debug::origin::ClauseOrigin {
                environment: Vec::new(),
                body: Vec::new(),
                head: debug::origin::Entry::parameter(TermVarIdx::from(0usize), &sort),
            },
            vars: vars.into_iter().collect(),
            head,
            body,
            debug_info: DebugInfo::default(),
        }
    }

    fn v(i: usize) -> Term {
        Term::var(i.into())
    }

    /// `x = 0 => P(x, x)`, and `P(x, y) ∧ step => P(x', y')` with the given step.
    fn loop_system(step: Formula) -> (System, PredVarId) {
        let mut system = System::default();
        let p = system.new_pred_var(vec![Sort::int(), Sort::int()], DebugInfo::default());
        system.push_clause(clause(
            vec![Sort::int()],
            Atom::new(Pred::Var(p), vec![v(0), v(0)]),
            Body::from(v(0).equal_to(Term::int(0))),
        ));
        system.push_clause(clause(
            vec![Sort::int(); 4],
            Atom::new(Pred::Var(p), vec![v(2), v(3)]),
            Body::new(vec![Atom::new(Pred::Var(p), vec![v(0), v(1)])], step),
        ));
        system.push_clause(clause(
            vec![Sort::int(); 2],
            Atom::bottom(),
            Body::new(
                vec![Atom::new(Pred::Var(p), vec![v(0), v(1)])],
                Formula::Atom(v(0).not_equal_to(v(1))),
            ),
        ));
        (system, p)
    }

    #[test]
    fn drops_a_column_the_loop_preserves() {
        let step = Formula::And(vec![
            Formula::Atom(v(2).equal_to(v(0).add(Term::int(1)))),
            Formula::Atom(v(3).equal_to(v(1).add(Term::int(1)))),
        ]);
        let (system, p) = loop_system(step);
        let system = dedup_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int()]);
        for clause in &system.clauses {
            for atom in clause.head_and_body_atoms() {
                assert_eq!(atom.args.len(), 1);
            }
        }
        // The goal clause `P(x, y) ∧ x ≠ y ⇒ ⊥` keeps `x = y` in its body.
        let goal = system.clauses.iter().last().unwrap();
        let kept = Formula::Atom(v(0).equal_to(v(1)));
        assert!(matches!(&goal.body.formula, Formula::And(fs) if fs.contains(&kept)));
    }

    #[test]
    fn restricted_to_loop_heads_leaves_other_predicates() {
        let step = Formula::And(vec![
            Formula::Atom(v(2).equal_to(v(0).add(Term::int(1)))),
            Formula::Atom(v(3).equal_to(v(1).add(Term::int(1)))),
        ]);
        let (mut system, p) = loop_system(step);
        // `x = 0 => Q(x, x)`: a non-recursive predicate with an established pair.
        let q = system.new_pred_var(vec![Sort::int(), Sort::int()], DebugInfo::default());
        system.push_clause(clause(
            vec![Sort::int()],
            Atom::new(Pred::Var(q), vec![v(0), v(0)]),
            Body::from(v(0).equal_to(Term::int(0))),
        ));
        let system = dedup_recursive_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int()]);
        assert_eq!(system.pred_vars[q].sig, vec![Sort::int(), Sort::int()]);
    }

    #[test]
    fn carries_an_equality_between_components_through_an_unflattened_predicate() {
        // x = (0, 0) => Q(x);  Q(x) => P(x.0, x.1);  P(a, b) ∧ Q(x) ∧ x = (a, b) => P(a, b)
        let pair = Sort::tuple(vec![Sort::int(), Sort::int()]);
        let mut system = System::default();
        let p = system.new_pred_var(vec![Sort::int(), Sort::int()], DebugInfo::default());
        let q = system.new_pred_var(vec![pair.clone()], DebugInfo::default());
        system.push_clause(clause(
            vec![pair.clone()],
            Atom::new(Pred::Var(q), vec![v(0)]),
            Body::from(v(0).equal_to(Term::tuple(vec![Term::int(0), Term::int(0)]))),
        ));
        system.push_clause(clause(
            vec![pair.clone()],
            Atom::new(Pred::Var(p), vec![v(0).tuple_proj(0), v(0).tuple_proj(1)]),
            Body::new(vec![Atom::new(Pred::Var(q), vec![v(0)])], Formula::top()),
        ));
        let system = dedup_recursive_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int(), Sort::int()]);
        assert_eq!(system.pred_vars[q].sig, vec![pair.clone()]);
        let system = dedup_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int()]);
        assert_eq!(system.pred_vars[q].sig, vec![pair]);
    }

    #[test]
    fn keeps_a_column_the_loop_changes() {
        let step = Formula::And(vec![
            Formula::Atom(v(2).equal_to(v(0).add(Term::int(1)))),
            Formula::Atom(v(3).equal_to(v(1).add(Term::int(2)))),
        ]);
        let (system, p) = loop_system(step);
        let system = dedup_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int(), Sort::int()]);
    }

    #[test]
    fn uses_an_equality_every_disjunct_establishes() {
        let step = |second: Term| {
            Formula::Or(vec![
                Formula::And(vec![
                    Formula::Atom(v(2).equal_to(v(0).add(Term::int(1)))),
                    Formula::Atom(v(3).equal_to(v(1).add(Term::int(1)))),
                ]),
                Formula::And(vec![
                    Formula::Atom(v(2).equal_to(v(0))),
                    Formula::Atom(v(3).equal_to(second)),
                ]),
            ])
        };
        let (system, p) = loop_system(step(v(1)));
        let system = dedup_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int()]);
        let (system, p) = loop_system(step(Term::int(0)));
        let system = dedup_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int(), Sort::int()]);
    }

    #[test]
    fn projections_of_a_constructed_tuple_are_its_components() {
        let pair = Sort::tuple(vec![Sort::int(), Sort::int()]);
        let mut system = System::default();
        let p = system.new_pred_var(vec![Sort::int(), Sort::int()], DebugInfo::default());
        // t = (x, x) => P(t.0, t.1)
        system.push_clause(clause(
            vec![pair, Sort::int()],
            Atom::new(Pred::Var(p), vec![v(0).tuple_proj(0), v(0).tuple_proj(1)]),
            Body::from(v(0).equal_to(Term::tuple(vec![v(1), v(1)]))),
        ));
        let system = dedup_pred_args(system);
        assert_eq!(system.pred_vars[p].sig, vec![Sort::int()]);
    }
}
