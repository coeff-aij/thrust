//! Whether a clause is definite in one user-defined predicate, for the derived predicates of
//! `crate::analyze::derived_pred`.

use std::collections::HashMap;

use super::{Atom, Clause, Formula, Pred, TermVarIdx, UserDefinedPred};

/// Whether a clause is definite in one predicate `pred`, the others fixed: read as the formula
/// `¬body ∨ head` and put in prenex conjunctive form, every conjunct has at most one positive
/// atom of `pred`, and none lies under an existential quantifier. Such a clause is a conjunction
/// of definite clauses `∀x. B ⇒ pred(t)` whose `B` is monotone in `pred`, the form whose
/// immediate-consequence operator is monotone and has a least fixed point.
///
/// The walk reads each connective as it acts in the clause: in a negative position (the body)
/// `∧` is a disjunction and `∀` an existential, by De Morgan. A predicate with a formula body is
/// followed into its body.
pub(super) struct DefiniteWalk<'a> {
    pred: &'a UserDefinedPred,
    bodies: &'a HashMap<&'a UserDefinedPred, &'a Formula>,
}

/// Not definite.
pub(super) struct Indefinite;

impl<'a> DefiniteWalk<'a> {
    pub(super) fn new(
        pred: &'a UserDefinedPred,
        bodies: &'a HashMap<&'a UserDefinedPred, &'a Formula>,
    ) -> Self {
        Self { pred, bodies }
    }

    /// Whether the clause concludes `pred` in what it checks: its head or a conjunct `¬ψ` of its
    /// body.
    pub(super) fn checks(mut self, clause: &'a Clause) -> bool {
        !matches!(self.concluding_parts(clause, true), Ok(0))
    }

    /// Whether the clause is definite in `pred`.
    pub(super) fn clause(mut self, clause: &'a Clause) -> bool {
        matches!(self.concluding_parts(clause, false), Ok(n) if n <= 1)
    }

    /// The parts of the clause, the disjuncts of `¬body ∨ head`, that conclude `pred`: its head
    /// and its body's atoms and conjuncts, or with `only_checks` its head and the `ψ` of each
    /// conjunct `¬ψ`.
    fn concluding_parts(
        &mut self,
        clause: &'a Clause,
        only_checks: bool,
    ) -> Result<usize, Indefinite> {
        let mut conjuncts = Vec::new();
        clause.body.formula.conjuncts_into(&mut conjuncts);
        let mut concluding = usize::from(self.atom(&clause.head, true)?);
        if !only_checks {
            for atom in &clause.body.atoms {
                concluding += usize::from(self.atom(atom, false)?);
            }
        }
        for conjunct in conjuncts {
            let part = match (conjunct, only_checks) {
                (Formula::Not(psi), true) => self.formula(psi, true)?,
                (_, true) => false,
                (f, false) => self.formula(f, false)?,
            };
            concluding += usize::from(part);
        }
        Ok(concluding)
    }

    /// Whether `formula`, at the polarity `positive` in the clause, contains a positive atom of
    /// `pred`; an error if it is not definite in `pred`.
    fn formula(&mut self, formula: &'a Formula, positive: bool) -> Result<bool, Indefinite> {
        match formula {
            Formula::Atom(atom) => self.atom(atom, positive),
            Formula::Not(f) => self.formula(f, !positive),
            Formula::And(fs) if positive => self.all(fs.iter().map(|f| (f, true))),
            Formula::And(fs) => self.any(fs.iter().map(|f| (f, false))),
            Formula::Or(fs) if positive => self.any(fs.iter().map(|f| (f, true))),
            Formula::Or(fs) => self.all(fs.iter().map(|f| (f, false))),
            Formula::Implies(lhs, rhs) if positive => {
                self.any([(&**lhs, false), (&**rhs, true)].into_iter())
            }
            Formula::Implies(lhs, rhs) => self.all([(&**lhs, true), (&**rhs, false)].into_iter()),
            Formula::Forall(_, f) => self.quantified(f, positive, !positive),
            Formula::Exists(_, f) => self.quantified(f, positive, positive),
        }
    }

    /// A quantifier over `body`, existential in the clause when `existential` holds.
    fn quantified(
        &mut self,
        body: &'a Formula,
        positive: bool,
        existential: bool,
    ) -> Result<bool, Indefinite> {
        let concludes = self.formula(body, positive)?;
        if existential && concludes {
            return Err(Indefinite);
        }
        Ok(concludes)
    }

    /// A conjunction in the clause: definite when each part is.
    fn all(
        &mut self,
        parts: impl Iterator<Item = (&'a Formula, bool)>,
    ) -> Result<bool, Indefinite> {
        let mut concludes = false;
        for (f, positive) in parts {
            concludes |= self.formula(f, positive)?;
        }
        Ok(concludes)
    }

    /// A disjunction in the clause: definite when each part is and at most one concludes.
    fn any(
        &mut self,
        parts: impl Iterator<Item = (&'a Formula, bool)>,
    ) -> Result<bool, Indefinite> {
        let mut concluding = 0;
        for (f, positive) in parts {
            if self.formula(f, positive)? {
                concluding += 1;
            }
        }
        if concluding > 1 {
            return Err(Indefinite);
        }
        Ok(concluding == 1)
    }

    fn atom(&mut self, atom: &'a Atom<TermVarIdx>, positive: bool) -> Result<bool, Indefinite> {
        let Pred::UserDefined(pred) = &atom.pred else {
            return Ok(false);
        };
        if pred == self.pred {
            return Ok(positive);
        }
        // A predicate does not call itself (`annot_fn` rejects it; a recursive definition is a
        // logic function, whose body is a term), so following the bodies terminates.
        match self.bodies.get(pred).copied() {
            Some(body) => self.formula(body, positive),
            None => Ok(false),
        }
    }
}
