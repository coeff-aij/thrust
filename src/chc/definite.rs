//! Whether a clause is definite in one user-defined predicate, for the derived predicates of
//! `crate::analyze::derived_pred`.

use std::collections::{HashMap, HashSet};

use super::{Atom, Clause, Formula, Pred, TermVarIdx, UserDefinedPred};
/// Whether a clause is definite in one predicate `pred`, the others fixed: read as the formula
/// `¬body ∨ head` and put in prenex conjunctive form, every conjunct has at most one positive
/// atom of `pred`, and none lies under an existential quantifier. Such a clause is a conjunction
/// of definite clauses `∀x. B ⇒ pred(t)` whose `B` is monotone in `pred`, the form whose
/// immediate-consequence operator is monotone and has a least fixed point.
///
/// The walk reads each connective as it acts in the clause: in a negative position (the body)
/// `∧` is a disjunction and `∀` an existential, by De Morgan. A predicate with a formula body is
/// followed into its body; one entered again (a recursive body) is definite only if its body
/// does not mention `pred`.
pub(super) struct DefiniteWalk<'a> {
    pred: &'a UserDefinedPred,
    bodies: &'a HashMap<&'a UserDefinedPred, &'a Formula>,
    entered: HashSet<&'a UserDefinedPred>,
}

/// Not definite.
pub(super) struct Indefinite;

impl<'a> DefiniteWalk<'a> {
    pub(super) fn new(
        pred: &'a UserDefinedPred,
        bodies: &'a HashMap<&'a UserDefinedPred, &'a Formula>,
    ) -> Self {
        Self {
            pred,
            bodies,
            entered: HashSet::new(),
        }
    }

    /// Whether the clause concludes `pred` in what it checks: its head or a conjunct `¬ψ` of its
    /// body.
    pub(super) fn checks(mut self, clause: &'a Clause) -> bool {
        let mut conjuncts = Vec::new();
        clause.body.formula.conjuncts_into(&mut conjuncts);
        let obligations = conjuncts.into_iter().filter_map(|f| match f {
            Formula::Not(psi) => Some(&**psi),
            _ => None,
        });
        let mut concludes = !matches!(self.atom(&clause.head, true), Ok(false));
        for psi in obligations {
            concludes |= !matches!(self.formula(psi, true), Ok(false));
        }
        concludes
    }

    pub(super) fn clause(mut self, clause: &'a Clause) -> bool {
        let head = std::iter::once((&clause.head, true));
        let body = clause.body.atoms.iter().map(|atom| (atom, false));
        let mut concluding = 0;
        for (atom, positive) in head.chain(body) {
            match self.atom(atom, positive) {
                Ok(true) => concluding += 1,
                Ok(false) => {}
                Err(Indefinite) => return false,
            }
        }
        match self.formula(&clause.body.formula, false) {
            Ok(true) => concluding += 1,
            Ok(false) => {}
            Err(Indefinite) => return false,
        }
        concluding <= 1
    }

    /// Whether `formula`, at the polarity `positive` in the clause, contains a positive atom of
    /// `pred`; an error if it is not definite in `pred`.
    pub(super) fn formula(
        &mut self,
        formula: &'a Formula,
        positive: bool,
    ) -> Result<bool, Indefinite> {
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
        let Some(body) = self.bodies.get(pred).copied() else {
            return Ok(false);
        };
        if !self.entered.insert(pred) {
            let mentions = body
                .iter_atoms()
                .any(|a| a.pred == Pred::UserDefined(self.pred.clone()));
            return if mentions { Err(Indefinite) } else { Ok(false) };
        }
        let concludes = self.formula(body, positive);
        self.entered.remove(pred);
        concludes
    }
}
