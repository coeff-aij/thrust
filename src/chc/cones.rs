//! The cone of each goal: the goal and, transitively, every clause whose head is an unknown the
//! bodies of the cone apply (`THRUST_SPLIT_GOALS`).
//!
//! The cones are solved on their own only when every clause is a definite Horn clause: a goal,
//! whose unknowns all occur in body positions (see [`super::prune`]), or a clause with exactly
//! one unknown in a head position, its head atom or a negated top-level body atom, and its other
//! unknowns in body positions. A system of such clauses is satisfiable exactly when each cone is,
//! the slicing of Z3's muZ (Hoder, Bjørner and de Moura, CAV 2011) and Eldarica (Hojjat and
//! Rümmer, FMCAD 2018), surveyed by De Angelis et al. (TPLP 2022):
//!
//! - its definite clauses have a least model, the intersection of all their models, and a goal,
//!   whose body is monotone in the unknowns, holds in some model exactly when it holds in the
//!   least one;
//! - the least model of a cone's definite clauses is that of the whole system restricted to the
//!   cone's unknowns, since the cone holds every clause whose head is one of them.
//!
//! So the verdict of each cone is that of its goals in the whole system: the system is `sat`
//! exactly when every cone is, and `unsat` when one is. The argument holds at each
//! interpretation of the forall predicates. There the least model's interpretation of an unknown
//! depends only on the forall predicates of the clauses that derive it, transitively, and the
//! dependency set it is declared with (`declare-dep-exists-fun`) holds those in a cone as in the
//! whole system (it also holds those of the conclusions that read it, which differ), so the least
//! model respects both declarations. Since the intersection of models is a
//! model, so is the conjunction of the interpretations the cones give an unknown they share.
//! A cone repeats the clauses it shares with other cones. An unknown applied in a definition or
//! a law, or a derived predicate, is in positions this does not follow, so such a system is not
//! split into cones.

use std::collections::{HashMap, HashSet};

use super::prune::{clause_occurrences, Occurrence, Position};
use super::*;

/// Why a system is not split into the cones of its goals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotHorn {
    /// An unknown is applied in the body of a user-defined predicate or in a law.
    InDefinition,
    /// A derived predicate is an unknown of the system.
    Derived,
    /// The clause has several unknowns in head positions, or one under a guard or a quantifier.
    Clause(ClauseId),
}

/// The unknown in the head position of a definite clause, `None` for a goal.
fn head(
    id: ClauseId,
    clause: &Clause,
    occurrences: &[Occurrence],
) -> Result<Option<PredVarId>, NotHorn> {
    let mut heads = occurrences.iter().filter(|o| o.position == Position::Head);
    match (heads.next(), heads.next()) {
        (None, _) => Ok(None),
        (Some(o), None) if o.top_level || clause.head.pred == Pred::Var(o.pred) => Ok(Some(o.pred)),
        _ => Err(NotHorn::Clause(id)),
    }
}

impl System {
    /// The cone of each goal, in the order of the goals, each in the order of its clauses.
    pub fn goal_cones(&self) -> Result<Vec<Vec<ClauseId>>, NotHorn> {
        let in_laws = self.laws.values().flatten().flat_map(Formula::iter_atoms);
        if !self.pred_vars_in_definitions().is_empty()
            || in_laws
                .into_iter()
                .any(|atom| matches!(atom.pred, Pred::Var(_)))
        {
            return Err(NotHorn::InDefinition);
        }
        if self
            .user_defined_pred_defs
            .iter()
            .any(|def| def.is_derived())
        {
            return Err(NotHorn::Derived);
        }
        let occurrences: HashMap<ClauseId, Vec<Occurrence>> = self
            .clauses
            .iter_enumerated()
            .filter(|(_, clause)| !clause.is_nop())
            .map(|(id, clause)| (id, clause_occurrences(clause)))
            .collect();
        let mut defining: HashMap<PredVarId, Vec<ClauseId>> = HashMap::new();
        let mut goals = Vec::new();
        for (id, clause) in self.clauses.iter_enumerated() {
            let Some(occurrences) = occurrences.get(&id) else {
                continue;
            };
            match head(id, clause, occurrences)? {
                Some(p) => defining.entry(p).or_default().push(id),
                None => goals.push(id),
            }
        }
        let cone = |goal: ClauseId| {
            let mut clauses = HashSet::from([goal]);
            let mut applied = HashSet::new();
            let mut pending = vec![goal];
            while let Some(id) = pending.pop() {
                let in_body = occurrences[&id]
                    .iter()
                    .filter(|o| o.position == Position::Body);
                for o in in_body {
                    if !applied.insert(o.pred) {
                        continue;
                    }
                    for &c in defining.get(&o.pred).into_iter().flatten() {
                        if clauses.insert(c) {
                            pending.push(c);
                        }
                    }
                }
            }
            let mut clauses: Vec<ClauseId> = clauses.into_iter().collect();
            clauses.sort_by_key(|id| id.index());
            clauses
        };
        Ok(goals.into_iter().map(cone).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(head: Atom<TermVarIdx>, body: Vec<Atom<TermVarIdx>>, formula: Formula) -> Clause {
        Clause {
            origin: debug::origin::ClauseOrigin {
                environment: Vec::new(),
                body: Vec::new(),
                head: debug::origin::Entry::described(String::new()),
            },
            vars: IndexVec::new(),
            head,
            body: Body::new(body, formula),
            debug_info: DebugInfo::default(),
        }
    }

    fn atom(p: PredVarId) -> Atom<TermVarIdx> {
        Atom::new(p.into(), vec![])
    }

    /// `p ⇐ ⊤`, `q ⇐ p`, `r ⇐ ⊤`, `⊥ ⇐ q`, `⊥ ⇐ q ∧ r`, `s ⇐ ⊤` (no goal applies `s`).
    fn two_goals() -> (System, [ClauseId; 6]) {
        let mut system = System::default();
        let [p, q, r, s] = [(); 4].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let mut push = |c| system.push_clause(c).unwrap();
        let ids = [
            push(clause(atom(p), vec![], Formula::top())),
            push(clause(atom(q), vec![atom(p)], Formula::top())),
            push(clause(atom(r), vec![], Formula::top())),
            push(clause(Atom::bottom(), vec![atom(q)], Formula::top())),
            push(clause(
                Atom::bottom(),
                vec![atom(q), atom(r)],
                Formula::top(),
            )),
            push(clause(atom(s), vec![], Formula::top())),
        ];
        (system, ids)
    }

    #[test]
    fn a_cone_holds_the_clauses_deriving_its_goal_s_unknowns() {
        let (system, [c0, c1, c2, c3, c4, _]) = two_goals();
        let cones = system.goal_cones().unwrap();
        assert_eq!(cones, vec![vec![c0, c1, c3], vec![c0, c1, c2, c4]]);
    }

    #[test]
    fn a_negated_body_atom_is_the_head_of_a_definite_clause() {
        let mut system = System::default();
        let [p, q] = [(); 2].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let negated = Formula::Atom(atom(q)).not();
        let c0 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)], negated))
            .unwrap();
        let c1 = system
            .push_clause(clause(Atom::bottom(), vec![atom(q)], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap(), vec![vec![c0, c1]]);
    }

    #[test]
    fn two_unknowns_in_head_positions_are_no_horn_clause() {
        let mut system = System::default();
        let [p, q] = [(); 2].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let negated = Formula::Atom(atom(q)).not();
        let c0 = system
            .push_clause(clause(atom(p), vec![], negated))
            .unwrap();
        assert_eq!(system.goal_cones(), Err(NotHorn::Clause(c0)));
    }

    #[test]
    fn an_existential_head_is_no_horn_clause() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let exists = Formula::Exists(vec![], Box::new(Formula::Atom(atom(p))));
        let c0 = system
            .push_clause(clause(Atom::bottom(), vec![], exists.not()))
            .unwrap();
        assert_eq!(system.goal_cones(), Err(NotHorn::Clause(c0)));
    }

    #[test]
    fn an_unknown_in_a_definition_is_not_followed() {
        let (mut system, _) = two_goals();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let symbol = UserDefinedPred::new("holds".into());
        system.push_pred_define_formula(symbol, IndexVec::new(), Formula::Atom(atom(p)));
        assert_eq!(system.goal_cones(), Err(NotHorn::InDefinition));
    }
}
