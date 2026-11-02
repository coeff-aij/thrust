//! The cone of each goal: the goal and, transitively, every clause whose head is an unknown the
//! bodies of the cone apply (`THRUST_SPLIT_GOALS`).
//!
//! The cones are solved on their own only when every clause is definite: read as `¬body ∨ head`,
//! with the guard of an atom as a premise of it, it is a conjunction of clauses each with at most
//! one unknown in its head and the others in body positions (see [`super::prune`]). A `∀` in a
//! head position distributes over that conjunction and its variables become the clause's
//! (`body ⇒ ∀x. p(x)`); a disjunction in a head position holds at most one unknown
//! (`body ⇒ p(x) ∨ c` is `body ∧ ¬c ⇒ p(x)`); an unknown under an `∃` in a head position is not
//! definite. A clause that also states a constraint (`body ⇒ p(x) ∧ c`) derives `p` and is a goal
//! too. Solving each cone on its own then gives the verdict of the system, as the slicing of Z3's
//! muZ (Hoder, Bjørner and de Moura, CAV 2011) and Eldarica (Hojjat and Rümmer, FMCAD 2018),
//! surveyed by De Angelis et al. (TPLP 2022), at each interpretation of the forall predicates:
//!
//! - `sat` when every cone is: the models of definite clauses are closed under intersection, so
//!   the conjunction of the interpretations the cones give an unknown is a model of every cone (a
//!   cone that applies an unknown holds every clause deriving it, and a body position takes the
//!   conjunction as a stronger premise), and an unknown in no cone, which no goal reads, is
//!   interpreted as `true`. A cone's dependency set of an unknown (`declare-dep-exists-fun`) is a
//!   subset of the whole system's, so the conjunction respects the latter.
//! - `unsat` when a cone is: the definite clauses have a least model, the intersection of all
//!   their models, whose interpretation of an unknown in a cone is the least model of the cone's
//!   definite clauses, and depends only on the forall predicates of the clauses deriving it,
//!   which its dependency set holds in a cone as in the whole system; a goal, monotone in the
//!   unknowns, holds in some model exactly when it holds in the least one.
//!
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
    /// The clause has a disjunction of unknowns in a head position, or an unknown under an `∃` in
    /// a head position.
    Clause(ClauseId),
}

/// The unknowns a formula read in a head position derives, and whether it states a constraint
/// besides them; an unknown under `∃` or in a disjunction with another is `Err`.
#[derive(Debug, Default)]
struct Heads {
    unknowns: Vec<PredVarId>,
    constraint: bool,
}

fn all_of(heads: impl IntoIterator<Item = Result<Heads, ()>>) -> Result<Heads, ()> {
    let mut all = Heads::default();
    for h in heads {
        let h = h?;
        all.unknowns.extend(h.unknowns);
        all.constraint |= h.constraint;
    }
    Ok(all)
}

fn any_of(heads: impl IntoIterator<Item = Result<Heads, ()>>) -> Result<Heads, ()> {
    let mut any = Heads {
        unknowns: Vec::new(),
        constraint: true,
    };
    for h in heads {
        let h = h?;
        if !h.unknowns.is_empty() && !any.unknowns.is_empty() {
            return Err(());
        }
        any.unknowns.extend(h.unknowns);
        any.constraint &= h.constraint;
    }
    Ok(any)
}

/// The heads of `atom` in a head position (`in_head`) or of its negation in a body position.
fn atom_heads(atom: &Atom, in_head: bool) -> Result<Heads, ()> {
    let applied = match atom.pred {
        Pred::Var(p) if in_head => Heads {
            unknowns: vec![p],
            constraint: false,
        },
        _ => Heads {
            unknowns: Vec::new(),
            constraint: true,
        },
    };
    let Some(guard) = &atom.guard else {
        return Ok(applied);
    };
    // `guard ⇒ atom` is `¬guard ∨ atom`, and its negation `guard ∧ ¬atom`.
    if in_head {
        any_of([formula_heads(guard, false), Ok(applied)])
    } else {
        all_of([formula_heads(guard, true), Ok(applied)])
    }
}

/// The heads of `formula` in a head position (`in_head`) or of its negation in a body position.
fn formula_heads(formula: &Formula, in_head: bool) -> Result<Heads, ()> {
    let each = |fs: &[Formula]| -> Vec<Result<Heads, ()>> {
        fs.iter().map(|f| formula_heads(f, in_head)).collect()
    };
    match (formula, in_head) {
        (Formula::Atom(atom), _) => atom_heads(atom, in_head),
        (Formula::Not(f), _) => formula_heads(f, !in_head),
        (Formula::And(fs), true) | (Formula::Or(fs), false) => all_of(each(fs)),
        (Formula::Or(fs), true) | (Formula::And(fs), false) => any_of(each(fs)),
        (Formula::Implies(lhs, rhs), true) => {
            any_of([formula_heads(lhs, false), formula_heads(rhs, true)])
        }
        (Formula::Implies(lhs, rhs), false) => {
            all_of([formula_heads(lhs, true), formula_heads(rhs, false)])
        }
        (Formula::Forall(_, f), true) | (Formula::Exists(_, f), false) => formula_heads(f, in_head),
        (Formula::Exists(_, f), true) | (Formula::Forall(_, f), false) => {
            let heads = formula_heads(f, in_head)?;
            if heads.unknowns.is_empty() {
                Ok(heads)
            } else {
                Err(())
            }
        }
    }
}

/// The unknowns `clause`, read as `¬body ∨ head`, derives, and whether it is a goal.
fn clause_heads(id: ClauseId, clause: &Clause) -> Result<Heads, NotHorn> {
    let premises = clause
        .body
        .atoms
        .iter()
        .map(|atom| atom_heads(atom, false))
        .chain([formula_heads(&clause.body.formula, false)]);
    let head = atom_heads(&clause.head, true);
    any_of(premises.chain([head])).map_err(|()| NotHorn::Clause(id))
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
            if !occurrences.contains_key(&id) {
                continue;
            }
            let heads = clause_heads(id, clause)?;
            for p in heads.unknowns {
                defining.entry(p).or_default().push(id);
            }
            if heads.constraint {
                goals.push(id);
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
    fn a_disjunction_of_unknowns_in_head_positions_is_no_horn_clause() {
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

    #[test]
    fn a_derived_predicate_is_not_followed() {
        let (mut system, _) = two_goals();
        system.push_derived_pred(UserDefinedPred::new("derived".into()), Vec::new());
        assert_eq!(system.goal_cones(), Err(NotHorn::Derived));
    }

    #[test]
    fn the_guard_of_a_head_atom_is_a_premise() {
        let mut system = System::default();
        let [p, q] = [(); 2].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let guarded = Atom::with_guard(Formula::Atom(atom(q)), p.into(), vec![]);
        let c0 = system
            .push_clause(clause(atom(q), vec![], Formula::top()))
            .unwrap();
        let c1 = system
            .push_clause(clause(guarded, vec![], Formula::top()))
            .unwrap();
        let c2 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap(), vec![vec![c0, c1, c2]]);
    }

    /// `⊥ ⇐ ¬∀. p` is `p ⇐ ⊤` with the quantified variables as the clause's.
    #[test]
    fn a_universal_head_derives_its_unknown() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let forall = Formula::Forall(vec![], Box::new(Formula::Atom(atom(p))));
        let c0 = system
            .push_clause(clause(Atom::bottom(), vec![], forall.not()))
            .unwrap();
        let c1 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap(), vec![vec![c0, c1]]);
    }

    /// `⊥ ⇐ ¬(p ∧ c)` is `p ⇐ ⊤` and the goal `c ⇐ ⊤`: it derives `p` and is a goal.
    #[test]
    fn a_head_with_a_constraint_derives_and_is_a_goal() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let both = Formula::And(vec![Formula::Atom(atom(p)), Formula::Atom(Atom::bottom())]);
        let c0 = system
            .push_clause(clause(Atom::bottom(), vec![], both.not()))
            .unwrap();
        let c1 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap(), vec![vec![c0], vec![c0, c1]]);
    }
}
