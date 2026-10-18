//! The independent parts of a system: the classes of clauses that share a predicate variable.
//!
//! Two clauses without a common unknown constrain disjoint sets of unknowns, so the system has a
//! solution exactly when each class has one: a solution of each class, joined, solves the whole,
//! and a solution of the whole restricts to each class. A forall predicate is not an unknown (the
//! system must hold for every interpretation of it), so sharing one does not join two classes:
//! for every interpretation of the forall predicates, the classes are solved independently.
//!
//! An unknown can also occur in the body of a user-defined predicate, directly or through the
//! predicates it calls; a clause applying such a predicate is joined with the unknowns it reaches.
//! A law of a forall predicate applies no unknown: the query states the laws before it declares
//! the unknowns. A written contract carries no unknown, so the classes are cut at the functions
//! whose contracts are written.

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

/// The unknowns the body of each user-defined predicate applies, directly or through the
/// predicates it calls.
fn reached_pred_vars(system: &System) -> HashMap<&UserDefinedPred, HashSet<PredVarId>> {
    let applied = |def: &UserDefinedPredDef| match &def.body {
        UserDefinedPredBody::Formula(formula) => formula
            .iter_atoms()
            .filter_map(|atom| match atom.pred {
                Pred::Var(p) => Some(p),
                _ => None,
            })
            .collect(),
        UserDefinedPredBody::Raw(_) | UserDefinedPredBody::Term(..) => Vec::new(),
    };
    let defs: HashMap<&UserDefinedPred, &UserDefinedPredDef> = system
        .user_defined_pred_defs
        .iter()
        .map(|def| (&def.symbol, def))
        .collect();
    let calls: HashMap<&UserDefinedPred, HashSet<&UserDefinedPred>> = defs
        .iter()
        .map(|(symbol, def)| (*symbol, def.callees().into_iter().collect()))
        .collect();
    let called = compute_transitive_closure(&calls);
    defs.iter()
        .map(|(symbol, def)| {
            let callees = called[symbol].iter().filter_map(|c| defs.get(c).copied());
            let pred_vars = std::iter::once(*def).chain(callees).flat_map(applied);
            (*symbol, pred_vars.collect())
        })
        .collect()
}

/// The classes of the clauses of `system` that share an unknown, each in the order of the
/// clauses, and the classes in the order of their first clause.
pub fn components(system: &System) -> Vec<Vec<ClauseId>> {
    let reached = reached_pred_vars(system);
    // A node per clause, then one per unknown.
    let clause_count = system.clauses.len();
    let mut classes = UnionFind::new(clause_count + system.pred_vars.len());
    for (id, clause) in system.clauses.iter_enumerated() {
        let atoms = std::iter::once(&clause.head)
            .chain(&clause.body.atoms)
            .chain(clause.body.formula.iter_atoms());
        let through_definitions = user_defined_in(atoms)
            .into_iter()
            .filter_map(|symbol| reached.get(symbol))
            .flatten()
            .copied();
        let applied = prune::pred_vars_of(std::iter::once(clause));
        for p in applied.into_iter().chain(through_definitions) {
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

/// The user-defined predicates and functions the clauses `ids` apply, and with them those the
/// laws, the raw commands and the candidate atoms apply, closed under the definitions' callees (a
/// raw body or command by the names its text mentions).
fn reached_definitions(system: &System, ids: &[ClauseId]) -> HashSet<UserDefinedPred> {
    let defs: Vec<(&UserDefinedPredDef, String)> = system
        .user_defined_pred_defs
        .iter()
        .map(|def| (def, def.symbol.to_string()))
        .collect();
    let named_in = |text: &str| -> Vec<UserDefinedPred> {
        defs.iter()
            .filter(|(_, name)| text.contains(name.as_str()))
            .map(|(def, _)| def.symbol.clone())
            .collect()
    };
    let clauses = ids.iter().map(|&id| &system.clauses[id]);
    let clause_atoms = clauses.flat_map(|c| {
        std::iter::once(&c.head)
            .chain(&c.body.atoms)
            .chain(c.body.formula.iter_atoms())
    });
    let law_atoms = system.laws.values().flatten().flat_map(Formula::iter_atoms);
    // The candidates of the part's unknowns only.
    let unknowns = system.pred_vars_of(ids);
    let candidate_atoms = system
        .candidate_atoms
        .iter()
        .filter(|c| unknowns.contains(&c.pred))
        .flat_map(|c| c.atoms.iter().flat_map(Formula::iter_atoms));
    let mut pending: Vec<UserDefinedPred> = user_defined_in(clause_atoms)
        .into_iter()
        .chain(user_defined_in(law_atoms))
        .chain(user_defined_in(candidate_atoms))
        .cloned()
        .collect();
    for raw in &system.raw_commands {
        pending.extend(named_in(&raw.command));
    }
    let mut reached = HashSet::new();
    while let Some(symbol) = pending.pop() {
        if !reached.insert(symbol.clone()) {
            continue;
        }
        let Some((def, _)) = defs.iter().find(|(def, _)| def.symbol == symbol) else {
            continue;
        };
        pending.extend(def.callees().into_iter().cloned());
        if let UserDefinedPredBody::Raw(text) = &def.body {
            pending.extend(named_in(text));
        }
    }
    reached
}

impl System {
    /// The unknowns the clauses `ids` apply.
    pub fn pred_vars_of(&self, ids: &[ClauseId]) -> HashSet<PredVarId> {
        prune::pred_vars_of(ids.iter().map(|&id| &self.clauses[id]))
    }

    /// The system with only the clauses `ids`; each other clause is replaced by `true ⇐ true`,
    /// which the query leaves out, so that every clause keeps its id. Of the definitions, it
    /// keeps those the clauses reach, so that a part declares no sort (a sequence) it does not
    /// use.
    pub fn part(&self, ids: &[ClauseId]) -> System {
        let kept: HashSet<ClauseId> = ids.iter().copied().collect();
        let mut system = self.clone();
        let reached = reached_definitions(self, ids);
        system
            .user_defined_pred_defs
            .retain(|def| reached.contains(&def.symbol));
        for id in self.clauses.indices() {
            if !kept.contains(&id) {
                system.clauses[id] = Clause {
                    origin: debug::origin::ClauseOrigin {
                        environment: Vec::new(),
                        body: Vec::new(),
                        head: debug::origin::Entry::described("left out of the part".to_owned()),
                    },
                    vars: IndexVec::new(),
                    head: Atom::top(),
                    body: Body::top(),
                    debug_info: DebugInfo::default(),
                };
            }
        }
        // An unknown the part's query does not declare has no sorts there, so that the part
        // declares no datatype (a sequence) only another part applies.
        let emitted = prune::emitted_clauses(&system);
        let mut declared = prune::pred_vars_of(emitted.iter().map(|&id| &system.clauses[id]));
        declared.extend(system.pred_vars_in_definitions());
        for (p, def) in system.pred_vars.iter_enumerated_mut() {
            if !declared.contains(&p) {
                def.sig.clear();
            }
        }
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

    #[test]
    fn an_unknown_a_callee_applies_joins_the_callers() {
        let mut system = System::default();
        let [p, q] = [(); 2].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let inner = UserDefinedPred::new("inner".into());
        let outer = UserDefinedPred::new("outer".into());
        system.push_pred_define_formula(inner.clone(), IndexVec::new(), Formula::Atom(atom(p)));
        let calls_inner = Formula::Atom(Atom::new(Pred::UserDefined(inner), vec![]));
        system.push_pred_define_formula(outer.clone(), IndexVec::new(), calls_inner);
        let c0 = system.push_clause(clause(atom(p), vec![])).unwrap();
        let c1 = system.push_clause(clause(atom(q), vec![])).unwrap();
        let applies = Atom::new(Pred::UserDefined(outer), vec![]);
        let c2 = system
            .push_clause(clause(Atom::bottom(), vec![applies]))
            .unwrap();
        assert_eq!(components(&system), vec![vec![c0, c2], vec![c1]]);
    }
}
