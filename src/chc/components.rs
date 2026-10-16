//! The independent parts of a system: the classes of clauses that share a predicate variable.
//!
//! Two clauses without a common unknown constrain disjoint sets of unknowns, so the system has a
//! solution exactly when each class has one: a solution of each class, joined, solves the whole,
//! and a solution of the whole restricts to each class. A forall predicate is not an unknown (the
//! system must hold for every interpretation of it), so sharing one does not join two classes:
//! for every interpretation of the forall predicates, the classes are solved independently.
//!
//! An unknown can also occur outside the clauses: in the body of a user-defined predicate
//! (through the predicates it calls) and in the laws of a forall predicate. A clause applying such
//! a predicate is joined with the unknowns it carries. A written contract carries no unknown, so
//! the classes are cut at the functions whose contracts are written.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::*;

struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
        }
    }

    fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut x = x;
        while self.parent[x] != root {
            let next = self.parent[x];
            self.parent[x] = root;
            x = next;
        }
        root
    }

    fn union(&mut self, a: usize, b: usize) {
        let (a, b) = (self.find(a), self.find(b));
        if a != b {
            self.parent[a.max(b)] = a.min(b);
        }
    }
}

/// What a clause applies besides its own unknowns: the user-defined predicates and functions and
/// the forall predicates, read through every atom and term.
#[derive(Default)]
struct Applied<'a> {
    pred_vars: Vec<PredVarId>,
    user_defined: Vec<&'a UserDefinedPred>,
    forall: Vec<&'a ForallPred>,
}

impl<'a> Applied<'a> {
    fn term(&mut self, term: &'a Term<TermVarIdx>) {
        for t in term.preorder() {
            match t {
                Term::UserDefinedFn(symbol, _, _) => self.user_defined.push(symbol),
                Term::ForallFn(pred, _) => self.forall.push(pred),
                _ => {}
            }
        }
    }

    fn atom(&mut self, atom: &'a Atom<TermVarIdx>) {
        match &atom.pred {
            Pred::Var(p) => self.pred_vars.push(*p),
            Pred::UserDefined(symbol) => self.user_defined.push(symbol),
            Pred::ForallPred(pred) => self.forall.push(pred),
            _ => {}
        }
        for arg in &atom.args {
            self.term(arg);
        }
        if let Some(guard) = &atom.guard {
            self.formula(guard);
        }
    }

    fn formula(&mut self, formula: &'a Formula<TermVarIdx>) {
        for atom in formula.iter_atoms() {
            self.atom(atom);
        }
    }

    fn clause(clause: &'a Clause) -> Self {
        let mut applied = Applied::default();
        applied.atom(&clause.head);
        for atom in &clause.body.atoms {
            applied.atom(atom);
        }
        applied.formula(&clause.body.formula);
        applied
    }
}

/// The unknowns each user-defined predicate reaches through its body and the predicates it calls.
fn user_defined_pred_vars(system: &System) -> HashMap<&UserDefinedPred, HashSet<PredVarId>> {
    let mut direct: HashMap<&UserDefinedPred, (HashSet<PredVarId>, Vec<&UserDefinedPred>)> =
        HashMap::new();
    for def in &system.user_defined_pred_defs {
        let pred_vars = match &def.body {
            UserDefinedPredBody::Formula(formula) => formula
                .iter_atoms()
                .filter_map(|atom| match atom.pred {
                    Pred::Var(p) => Some(p),
                    _ => None,
                })
                .collect(),
            UserDefinedPredBody::Raw(_) | UserDefinedPredBody::Term(..) => HashSet::new(),
        };
        direct.insert(&def.symbol, (pred_vars, def.callees()));
    }
    let mut reached: HashMap<&UserDefinedPred, HashSet<PredVarId>> = direct
        .iter()
        .map(|(symbol, (pred_vars, _))| (*symbol, pred_vars.clone()))
        .collect();
    loop {
        let mut changed = false;
        for (symbol, (_, callees)) in &direct {
            let mut from_callees: HashSet<PredVarId> = HashSet::new();
            for callee in callees {
                if let Some(pred_vars) = reached.get(callee) {
                    from_callees.extend(pred_vars);
                }
            }
            let mine = reached.get_mut(symbol).unwrap();
            let before = mine.len();
            mine.extend(from_callees);
            changed |= mine.len() != before;
        }
        if !changed {
            return reached;
        }
    }
}

/// The unknowns the laws of each forall predicate apply.
fn law_pred_vars(system: &System) -> HashMap<&ForallPred, HashSet<PredVarId>> {
    system
        .laws
        .iter()
        .map(|(pred, laws)| {
            let pred_vars = laws
                .iter()
                .flat_map(Formula::iter_atoms)
                .filter_map(|atom| match atom.pred {
                    Pred::Var(p) => Some(p),
                    _ => None,
                })
                .collect();
            (pred, pred_vars)
        })
        .collect()
}

/// The classes of the clauses of `system` that share an unknown, each in the order of the
/// clauses, and the classes in the order of their first clause.
pub fn components(system: &System) -> Vec<Vec<ClauseId>> {
    let by_user_defined = user_defined_pred_vars(system);
    let by_law = law_pred_vars(system);
    // A node per clause, then one per unknown.
    let clause_count = system.clauses.len();
    let mut classes = UnionFind::new(clause_count + system.pred_vars.len());
    for (id, clause) in system.clauses.iter_enumerated() {
        let applied = Applied::clause(clause);
        let carried = applied
            .user_defined
            .iter()
            .filter_map(|symbol| by_user_defined.get(symbol))
            .chain(applied.forall.iter().filter_map(|pred| by_law.get(pred)))
            .flatten();
        for p in applied.pred_vars.iter().chain(carried) {
            classes.union(id.index(), clause_count + p.index());
        }
    }
    let mut by_root: BTreeMap<usize, Vec<ClauseId>> = BTreeMap::new();
    for id in system.clauses.indices() {
        by_root
            .entry(classes.find(id.index()))
            .or_default()
            .push(id);
    }
    let mut components: Vec<Vec<ClauseId>> = by_root.into_values().collect();
    components.sort_by_key(|clauses| clauses[0].index());
    components
}

impl System {
    /// The system with only the clauses `ids`, renumbered in their order; every declaration is
    /// kept, and the query declares only the unknowns the remaining clauses apply.
    pub fn with_clauses(&self, ids: &[ClauseId]) -> System {
        let mut system = self.clone();
        system.clauses = ids.iter().map(|&id| self.clauses[id].clone()).collect();
        system
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(head: Atom<TermVarIdx>, body: Vec<Atom<TermVarIdx>>) -> Clause {
        Clause {
            origin: debug::origin::ClauseOrigin {
                environment: Vec::new(),
                body: Vec::new(),
                head: debug::origin::Entry::described(String::new()),
            },
            vars: IndexVec::new(),
            head,
            body: Body::new(body, Formula::top()),
            debug_info: DebugInfo::default(),
        }
    }

    fn atom(p: PredVarId) -> Atom<TermVarIdx> {
        Atom::new(p.into(), vec![])
    }

    #[test]
    fn clauses_sharing_an_unknown_form_one_part() {
        let mut system = System::default();
        let [p, q, r] = [(); 3].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let c0 = system.push_clause(clause(atom(p), vec![])).unwrap();
        let c1 = system.push_clause(clause(atom(q), vec![])).unwrap();
        let c2 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)]))
            .unwrap();
        let c3 = system.push_clause(clause(atom(r), vec![atom(q)])).unwrap();
        let c4 = system
            .push_clause(clause(Atom::bottom(), vec![atom(r)]))
            .unwrap();
        assert_eq!(components(&system), vec![vec![c0, c2], vec![c1, c3, c4]]);
    }

    #[test]
    fn an_unknown_in_a_definition_joins_the_clauses_applying_it() {
        let mut system = System::default();
        let [p, q] = [(); 2].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let symbol = UserDefinedPred::new("holds".into());
        system.push_pred_define_formula(symbol.clone(), IndexVec::new(), Formula::Atom(atom(p)));
        let c0 = system.push_clause(clause(atom(p), vec![])).unwrap();
        let c1 = system.push_clause(clause(atom(q), vec![])).unwrap();
        let applies = Atom::new(Pred::UserDefined(symbol), vec![]);
        let c2 = system
            .push_clause(clause(Atom::bottom(), vec![applies, atom(q)]))
            .unwrap();
        assert_eq!(components(&system), vec![vec![c0, c1, c2]]);
    }
}
