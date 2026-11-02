//! The cone of each goal: the goal and, transitively, every clause whose head is an unknown the
//! bodies of the cone apply (`THRUST_SPLIT_GOALS`).
//!
//! The cones are solved on their own only when every clause is definite: read as `¬body ∨ head`,
//! it is equivalent to a conjunction of clauses each with at most one unknown in its head and the
//! others in body positions (see [`super::prune`]), which the arguments below need. Each shape
//! accepted rewrites to that form by an equivalence of first-order logic:
//!
//! - `body ⇒ p(x)`, and `body ∧ ¬p(x) ⇒ ⊥`, a negated premise, which is the same clause;
//! - `body ⇒ (g ⇒ p(x))`, a guarded atom, which is `body ∧ g ⇒ p(x)`;
//! - `body ⇒ ∀y. p(x, y)`, which is `body ⇒ p(x, y)` with `y` a variable of the clause (`y` does
//!   not occur in `body`);
//! - `body ⇒ p(x) ∨ c` with no unknown in `c` in a head position, which is `body ∧ ¬c ⇒ p(x)`;
//! - `body ⇒ p(x) ∧ q(x) ∧ c`, which is `body ⇒ p(x)`, `body ⇒ q(x)` and the goal `body ⇒ c`:
//!   the clause derives `p` and `q` and is a goal too;
//! - a premise in which an unknown occurs only positively, under `∧`, `∨`, `∃` or `∀`, which keeps
//!   the body monotone in it.
//!
//! Refused: two unknowns in one head disjunction (`body ⇒ p(x) ∨ q(x)`, no least model) and an
//! unknown under an `∃` in a head position (`body ⇒ ∃y. p(x, y)`, whose models are not closed
//! under intersection). For a system of definite clauses, solving each cone on its own gives the
//! verdict of the system, as the slicing of Z3's muZ (Hoder, Bjørner and de Moura, CAV 2011) and
//! Eldarica (Hojjat and Rümmer, FMCAD 2018), surveyed by De Angelis et al. (TPLP 2022), at each
//! interpretation of the forall predicates:
//!
//! - `sat` when every cone is: the models of definite clauses are closed under intersection, and
//!   a cone that applies an unknown in a body position holds every clause deriving it, so the
//!   conjunction of the interpretations those cones give each unknown, `true` where none applies
//!   it, is a model of the system (a body position takes the conjunction as a stronger premise).
//!   A cone that has an unknown only in a head position (a goal that also derives it) may lack
//!   other clauses deriving it, so its interpretation is left out of the conjunction
//!   ([`System::deriving_clauses`]). A cone's dependency set of an unknown
//!   (`declare-dep-exists-fun`) is a subset of the whole system's, so the conjunction respects
//!   the latter.
//! - `unsat` when a cone is: the definite clauses have a least model, the intersection of all
//!   their models, whose interpretation of an unknown in a cone is the least model of the cone's
//!   definite clauses, and depends only on the forall predicates of the clauses deriving it,
//!   which its dependency set holds in a cone as in the whole system; a goal, monotone in the
//!   unknowns, holds in some model exactly when it holds in the least one.
//!
//! A clause that applies a definition whose body applies an unknown (a call's quantified
//! precondition, `pre_all(c) := ∀x. pre(c, x)`) is read with the definition unfolded: a
//! non-recursive definition is a macro, so the system with every such definition replaced by its
//! body is equivalent, and the shapes above, the positions of the unknowns and so the cones are
//! those of that system. Substitution keeps polarity: an unknown positive in the body of a
//! definition applied in a head position is in a head position, a negative one in a body
//! position, and the reverse where the definition is applied in a body position. The shape is
//! checked on each application, read as its body at the polarity of that application, so a
//! definition applied in both positions is accepted where each unfolding is, and a body that
//! puts an unknown under `∃` or in a disjunction with another is refused where it lands in a
//! head position. The query keeps the definitions, which the parts carry along with the clauses
//! that reach them. A definition that applies an unknown and itself, directly or through
//! others, would not unfold to a finite clause, and an unknown applied in a law or in raw
//! SMT-LIB text, directly or through a definition, or a derived predicate is in positions this
//! does not follow, so such a system is not split into cones. A
//! cone repeats the clauses it shares with other cones.

use std::collections::{HashMap, HashSet};

use super::prune::Position;
use super::*;

/// Why a system is not split into the cones of its goals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotHorn {
    /// An unknown is applied in a law or in raw SMT-LIB text, directly or through a definition.
    InLaw,
    /// A derived predicate is an unknown of the system.
    Derived,
    /// A definition that applies an unknown applies itself, directly or through others.
    RecursiveDefinition,
    /// The clause has a disjunction of unknowns in a head position, or an unknown under an `∃` in
    /// a head position.
    Clause(ClauseId),
}

/// The definitions with a formula body that applies an unknown, directly or through the
/// definitions it applies. A clause applying one is read with the definition unfolded.
struct Definitions<'a> {
    bodies: HashMap<&'a UserDefinedPred, &'a Formula>,
}

impl<'a> Definitions<'a> {
    fn new(system: &'a System) -> Self {
        let reached = components::reached_pred_vars(system);
        let bodies = system
            .user_defined_pred_defs
            .iter()
            .filter_map(|def| match &def.body {
                UserDefinedPredBody::Formula(body)
                    if reached.get(&def.symbol).is_some_and(|ps| !ps.is_empty()) =>
                {
                    Some((&def.symbol, body))
                }
                _ => None,
            })
            .collect();
        Definitions { bodies }
    }

    /// Whether a law or raw SMT-LIB text (a command or a definition's raw body) applies an
    /// unknown, directly or through a definition that is unfolded: it constrains the unknown
    /// outside every clause, where the cones do not follow it.
    fn applied_outside_clauses(&self, system: &System) -> bool {
        let law_atoms = || system.laws.values().flatten().flat_map(Formula::iter_atoms);
        let in_laws = user_defined_in(law_atoms());
        if law_atoms().any(|atom| matches!(atom.pred, Pred::Var(_)))
            || in_laws
                .iter()
                .any(|symbol| self.bodies.contains_key(symbol))
        {
            return true;
        }
        let raw_bodies = system
            .user_defined_pred_defs
            .iter()
            .filter_map(|def| match &def.body {
                UserDefinedPredBody::Raw(text) => Some(text.as_str()),
                _ => None,
            });
        let mut texts = system
            .raw_commands
            .iter()
            .map(|c| c.command.as_str())
            .chain(raw_bodies);
        let names: Vec<String> = self.bodies.keys().map(|s| s.to_string()).collect();
        texts.any(|text| names.iter().any(|name| text.contains(name.as_str())))
    }

    /// The body of the definition `atom` applies, when it is unfolded.
    fn unfolded(&self, atom: &Atom) -> Option<&'a Formula> {
        match &atom.pred {
            Pred::UserDefined(symbol) => self.bodies.get(symbol).copied(),
            _ => None,
        }
    }

    /// Whether a definition that is unfolded applies itself, so that unfolding does not end.
    fn recursive(&self) -> bool {
        let calls: HashMap<&UserDefinedPred, HashSet<&UserDefinedPred>> = self
            .bodies
            .iter()
            .map(|(symbol, body)| {
                let unfolded = user_defined_in(body.iter_atoms())
                    .into_iter()
                    .filter(|callee| self.bodies.contains_key(callee));
                (*symbol, unfolded.collect())
            })
            .collect();
        let called = compute_transitive_closure(&calls);
        called
            .iter()
            .any(|(symbol, callees)| callees.contains(symbol))
    }

    /// Each unknown `clause` applies with its position (see [`super::prune`]), the definitions
    /// unfolded; a definition entered again at the same position is not followed again.
    fn occurrences(&self, clause: &'a Clause) -> Vec<(PredVarId, Position)> {
        let mut walk = Occurrences {
            definitions: self,
            entered: HashSet::new(),
            found: Vec::new(),
        };
        walk.atom(&clause.head, Position::Head);
        for atom in &clause.body.atoms {
            walk.atom(atom, Position::Body);
        }
        walk.formula(&clause.body.formula, Position::Body);
        walk.found
    }
}

struct Occurrences<'a, 'd> {
    definitions: &'d Definitions<'a>,
    entered: HashSet<(&'a UserDefinedPred, Position)>,
    found: Vec<(PredVarId, Position)>,
}

impl<'a> Occurrences<'a, '_> {
    fn atom(&mut self, atom: &'a Atom, position: Position) {
        if let Some(guard) = &atom.guard {
            self.formula(guard, position.flip());
        }
        if let Pred::Var(p) = atom.pred {
            self.found.push((p, position));
        }
        let (Pred::UserDefined(symbol), Some(body)) = (&atom.pred, self.definitions.unfolded(atom))
        else {
            return;
        };
        if self.entered.insert((symbol, position)) {
            self.formula(body, position);
        }
    }

    fn formula(&mut self, formula: &'a Formula, position: Position) {
        match formula {
            Formula::Atom(atom) => self.atom(atom, position),
            Formula::Not(f) => self.formula(f, position.flip()),
            Formula::And(fs) | Formula::Or(fs) => fs.iter().for_each(|f| self.formula(f, position)),
            Formula::Implies(lhs, rhs) => {
                self.formula(lhs, position.flip());
                self.formula(rhs, position);
            }
            Formula::Exists(_, f) | Formula::Forall(_, f) => self.formula(f, position),
        }
    }
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

impl Definitions<'_> {
    /// The heads of `atom` in a head position (`in_head`) or of its negation in a body position;
    /// a definition that is unfolded is read as its body, which [`Self::recursive`] makes finite.
    fn atom_heads(&self, atom: &Atom, in_head: bool) -> Result<Heads, ()> {
        let applied = match (atom.pred.clone(), self.unfolded(atom)) {
            (_, Some(body)) => self.formula_heads(body, in_head)?,
            (Pred::Var(p), None) if in_head => Heads {
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
            any_of([self.formula_heads(guard, false), Ok(applied)])
        } else {
            all_of([self.formula_heads(guard, true), Ok(applied)])
        }
    }

    /// The heads of `formula` in a head position (`in_head`) or of its negation in a body
    /// position.
    fn formula_heads(&self, formula: &Formula, in_head: bool) -> Result<Heads, ()> {
        let each = |fs: &[Formula]| -> Vec<Result<Heads, ()>> {
            fs.iter().map(|f| self.formula_heads(f, in_head)).collect()
        };
        match (formula, in_head) {
            (Formula::Atom(atom), _) => self.atom_heads(atom, in_head),
            (Formula::Not(f), _) => self.formula_heads(f, !in_head),
            (Formula::And(fs), true) | (Formula::Or(fs), false) => all_of(each(fs)),
            (Formula::Or(fs), true) | (Formula::And(fs), false) => any_of(each(fs)),
            (Formula::Implies(lhs, rhs), true) => any_of([
                self.formula_heads(lhs, false),
                self.formula_heads(rhs, true),
            ]),
            (Formula::Implies(lhs, rhs), false) => all_of([
                self.formula_heads(lhs, true),
                self.formula_heads(rhs, false),
            ]),
            (Formula::Forall(_, f), true) | (Formula::Exists(_, f), false) => {
                self.formula_heads(f, in_head)
            }
            (Formula::Exists(_, f), true) | (Formula::Forall(_, f), false) => {
                let heads = self.formula_heads(f, in_head)?;
                if heads.unknowns.is_empty() {
                    Ok(heads)
                } else {
                    Err(())
                }
            }
        }
    }

    /// The unknowns `clause`, read as `¬body ∨ head`, derives, and whether it is a goal.
    fn clause_heads(&self, id: ClauseId, clause: &Clause) -> Result<Heads, NotHorn> {
        let premises = clause
            .body
            .atoms
            .iter()
            .map(|atom| self.atom_heads(atom, false))
            .chain([self.formula_heads(&clause.body.formula, false)]);
        let head = self.atom_heads(&clause.head, true);
        any_of(premises.chain([head])).map_err(|()| NotHorn::Clause(id))
    }
}

impl System {
    /// The cone of each goal, in the order of the goals, each in the order of its clauses.
    pub fn goal_cones(&self) -> Result<Vec<Vec<ClauseId>>, NotHorn> {
        if self
            .user_defined_pred_defs
            .iter()
            .any(|def| def.is_derived())
        {
            return Err(NotHorn::Derived);
        }
        let definitions = Definitions::new(self);
        if definitions.applied_outside_clauses(self) {
            return Err(NotHorn::InLaw);
        }
        if definitions.recursive() {
            return Err(NotHorn::RecursiveDefinition);
        }
        let occurrences = self.occurrences(&definitions);
        let mut goals = Vec::new();
        for (id, clause) in self.clauses.iter_enumerated() {
            if !occurrences.contains_key(&id) {
                continue;
            }
            if definitions.clause_heads(id, clause)?.constraint {
                goals.push(id);
            }
        }
        // Once every clause is definite, its unknowns in head positions are those it derives.
        let defining = deriving(&occurrences);
        let cone = |goal: ClauseId| {
            let mut clauses = HashSet::from([goal]);
            let mut applied = HashSet::new();
            let mut pending = vec![goal];
            while let Some(id) = pending.pop() {
                let in_body = occurrences[&id]
                    .iter()
                    .filter(|(_, position)| *position == Position::Body);
                for &(p, _) in in_body {
                    if !applied.insert(p) {
                        continue;
                    }
                    for &c in defining.get(&p).into_iter().flatten() {
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

    /// The clauses other than `true ⇐ …` and `… ⇐ false` in which each unknown occurs in a head
    /// position (see [`super::prune`]), the definitions they apply unfolded: those that derive
    /// it, from which the cones are built. A model of a part that holds all of them interprets
    /// the unknown as some model of the system does.
    pub fn deriving_clauses(&self) -> HashMap<PredVarId, HashSet<ClauseId>> {
        deriving(&self.occurrences(&Definitions::new(self)))
    }

    /// The unknowns each clause other than `true ⇐ …` and `… ⇐ false` applies, with their
    /// positions.
    fn occurrences<'a>(
        &'a self,
        definitions: &Definitions<'a>,
    ) -> HashMap<ClauseId, Vec<(PredVarId, Position)>> {
        self.clauses
            .iter_enumerated()
            .filter(|(_, clause)| !clause.is_nop())
            .map(|(id, clause)| (id, definitions.occurrences(clause)))
            .collect()
    }
}

fn deriving(
    occurrences: &HashMap<ClauseId, Vec<(PredVarId, Position)>>,
) -> HashMap<PredVarId, HashSet<ClauseId>> {
    let mut deriving: HashMap<PredVarId, HashSet<ClauseId>> = HashMap::new();
    for (&id, found) in occurrences {
        for &(p, position) in found {
            if position == Position::Head {
                deriving.entry(p).or_default().insert(id);
            }
        }
    }
    deriving
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
    fn an_unknown_in_an_applied_definition_joins_its_cone() {
        let (mut system, [c0, c1, c2, c3, c4, _]) = two_goals();
        let t = system.new_pred_var(vec![], DebugInfo::default());
        let symbol = UserDefinedPred::new("holds".into());
        system.push_pred_define_formula(symbol.clone(), IndexVec::new(), Formula::Atom(atom(t)));
        let applies = Atom::new(Pred::UserDefined(symbol), vec![]);
        let c6 = system
            .push_clause(clause(atom(t), vec![], Formula::top()))
            .unwrap();
        let c7 = system
            .push_clause(clause(Atom::bottom(), vec![applies], Formula::top()))
            .unwrap();
        let cones = system.goal_cones().unwrap();
        assert_eq!(
            cones,
            vec![vec![c0, c1, c3], vec![c0, c1, c2, c4], vec![c6, c7]]
        );
    }

    /// `pre_all := ∀. p` applied negated in a body (`⊥ ⇐ ¬pre_all`) derives `p`.
    #[test]
    fn a_definition_applied_negated_derives_its_unknown() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let symbol = UserDefinedPred::new("pre_all".into());
        let forall = Formula::Forall(vec![], Box::new(Formula::Atom(atom(p))));
        system.push_pred_define_formula(symbol.clone(), IndexVec::new(), forall);
        let applies = Formula::Atom(Atom::new(Pred::UserDefined(symbol), vec![]));
        let c0 = system
            .push_clause(clause(Atom::bottom(), vec![], applies.not()))
            .unwrap();
        let c1 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap(), vec![vec![c0, c1]]);
        assert_eq!(system.deriving_clauses()[&p], HashSet::from([c0]));
    }

    /// `either := p ∨ q` in a head position is a disjunction of unknowns once unfolded.
    #[test]
    fn a_definition_unfolds_to_the_shape_of_its_body() {
        let mut system = System::default();
        let [p, q] = [(); 2].map(|()| system.new_pred_var(vec![], DebugInfo::default()));
        let symbol = UserDefinedPred::new("either".into());
        let either = Formula::Or(vec![Formula::Atom(atom(p)), Formula::Atom(atom(q))]);
        system.push_pred_define_formula(symbol.clone(), IndexVec::new(), either);
        let applies = Atom::new(Pred::UserDefined(symbol), vec![]);
        let c0 = system
            .push_clause(clause(applies, vec![], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones(), Err(NotHorn::Clause(c0)));
    }

    /// `once := p` applied in a head position derives `p` and in a body position applies it;
    /// `some := ∃. p` applied in a head position is an existential head once unfolded.
    #[test]
    fn a_definition_applied_in_both_positions_has_the_shape_of_each_unfolding() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let once = UserDefinedPred::new("once".into());
        system.push_pred_define_formula(once.clone(), IndexVec::new(), Formula::Atom(atom(p)));
        let applies = Atom::new(Pred::UserDefined(once), vec![]);
        let c0 = system
            .push_clause(clause(
                Atom::bottom(),
                vec![],
                Formula::Atom(applies.clone()).not(),
            ))
            .unwrap();
        let c1 = system
            .push_clause(clause(Atom::bottom(), vec![applies], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap(), vec![vec![c0, c1]]);

        let some = UserDefinedPred::new("some".into());
        let exists = Formula::Exists(vec![], Box::new(Formula::Atom(atom(p))));
        system.push_pred_define_formula(some.clone(), IndexVec::new(), exists);
        let applies = Atom::new(Pred::UserDefined(some), vec![]);
        system
            .push_clause(clause(
                Atom::bottom(),
                vec![applies.clone()],
                Formula::top(),
            ))
            .unwrap();
        assert_eq!(system.goal_cones().unwrap().len(), 2);
        let c3 = system
            .push_clause(clause(applies, vec![], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones(), Err(NotHorn::Clause(c3)));
    }

    #[test]
    fn a_law_applying_an_unknown_through_a_definition_is_not_followed() {
        let (mut system, _) = two_goals();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let symbol = UserDefinedPred::new("holds".into());
        system.push_pred_define_formula(symbol.clone(), IndexVec::new(), Formula::Atom(atom(p)));
        let applies = Formula::Atom(Atom::new(Pred::UserDefined(symbol), vec![]));
        let q = ForallPred::new("q".into(), String::new(), vec![], vec![]);
        system.add_law(q, applies);
        assert_eq!(system.goal_cones(), Err(NotHorn::InLaw));
    }

    #[test]
    fn a_recursive_definition_applying_an_unknown_is_not_unfolded() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let symbol = UserDefinedPred::new("again".into());
        let applies = Atom::new(Pred::UserDefined(symbol.clone()), vec![]);
        let body = Formula::And(vec![Formula::Atom(atom(p)), Formula::Atom(applies.clone())]);
        system.push_pred_define_formula(symbol, IndexVec::new(), body);
        system
            .push_clause(clause(Atom::bottom(), vec![applies], Formula::top()))
            .unwrap();
        assert_eq!(system.goal_cones(), Err(NotHorn::RecursiveDefinition));
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

    /// `p(0) ∧ c ⇐ ⊤`, `p(1) ⇐ ⊤`, `⊥ ⇐ p`: the first is a goal whose cone lacks `p(1) ⇐ ⊤`.
    #[test]
    fn a_cone_with_an_unknown_only_in_a_head_lacks_its_other_derivations() {
        let mut system = System::default();
        let p = system.new_pred_var(vec![], DebugInfo::default());
        let both = Formula::And(vec![Formula::Atom(atom(p)), Formula::Atom(Atom::bottom())]);
        let c0 = system
            .push_clause(clause(Atom::bottom(), vec![], both.not()))
            .unwrap();
        let c1 = system
            .push_clause(clause(atom(p), vec![], Formula::top()))
            .unwrap();
        let c2 = system
            .push_clause(clause(Atom::bottom(), vec![atom(p)], Formula::top()))
            .unwrap();
        assert_eq!(
            system.goal_cones().unwrap(),
            vec![vec![c0], vec![c0, c1, c2]]
        );
        assert_eq!(system.deriving_clauses()[&p], HashSet::from([c0, c1]));
    }
}
