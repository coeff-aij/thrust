//! Which atoms of an assumption may depend on a derived predicate, for condition A of
//! `crate::analyze::derived_pred`.
//!
//! The set `D` of the predicates that may depend on a derived predicate `P` is closed under
//! definitions: `P` itself, every user-defined predicate or function whose body applies a member,
//! and every forall predicate or function whose instances may be such a definition (decided by
//! the caller, which knows where each forall predicate comes from). An assumption is walked with
//! its polarity, through the formula bodies known here; an atom of `P` must occur positively, and
//! any other member reached without a body to follow (a forall predicate, a term) is rejected
//! whatever its polarity, since its polarity towards `P` is not known.

use std::collections::{HashMap, HashSet};

use super::{
    Atom, ForallPred, Formula, Pred, System, Term, TermVarIdx, UserDefinedPred, UserDefinedPredBody,
};

/// What a forall predicate or function is with respect to the derived predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForallMember {
    /// No instance can depend on a derived predicate.
    Independent,
    /// A trait's predicate that is derived at some impl; its other instances are written. It
    /// depends on the derived predicate positively.
    Derived,
    /// An instance may depend on a derived predicate, with a polarity not known here.
    Dependent,
}

/// The members of `D` among the user-defined predicates of a system, with what the walk needs.
pub struct Dependence<'a> {
    derived: &'a HashSet<&'a UserDefinedPred>,
    bodies: HashMap<&'a UserDefinedPred, &'a Formula>,
    dependent: HashSet<&'a UserDefinedPred>,
    forall: &'a dyn Fn(&ForallPred) -> ForallMember,
}

impl System {
    /// The members of `D` among this system's user-defined predicates and functions, given the
    /// derived ones and what each forall predicate is (`forall`), to a fixed point.
    pub fn dependence<'a>(
        &'a self,
        derived: &'a HashSet<&'a UserDefinedPred>,
        forall: &'a dyn Fn(&ForallPred) -> ForallMember,
    ) -> Dependence<'a> {
        let bodies = self.formula_bodies();
        let mut dependence = Dependence {
            derived,
            bodies,
            dependent: derived.iter().copied().collect(),
            forall,
        };
        loop {
            let mut grown = false;
            for def in &self.user_defined_pred_defs {
                if dependence.dependent.contains(&def.symbol) {
                    continue;
                }
                let mentions = match &def.body {
                    UserDefinedPredBody::Formula(formula) => dependence.formula_mentions(formula),
                    UserDefinedPredBody::Term(_, term) => dependence.term_mentions(term),
                    // A raw SMT-LIB2 body cannot name a derived predicate, whose symbol is made
                    // from a hash and its instance; it is the user's text.
                    UserDefinedPredBody::Raw(_) => false,
                    UserDefinedPredBody::Derived => true,
                };
                if mentions {
                    dependence.dependent.insert(&def.symbol);
                    grown = true;
                }
            }
            if !grown {
                return dependence;
            }
        }
    }
}

impl<'a> Dependence<'a> {
    /// What in `formula`, read as an assumption, breaks condition A: a derived predicate
    /// negated, or a member of `D` whose polarity towards it is not known. With
    /// `forall_exempt`, forall predicates and functions are not looked at (a generic body's own
    /// precondition, verified for every interpretation).
    pub fn violations(&self, formula: &'a Formula, forall_exempt: bool) -> Vec<String> {
        let mut out = Vec::new();
        self.walk(formula, false, forall_exempt, &mut out);
        out
    }

    /// `positive` is the polarity in the clause read as `¬body ∨ head`: an assumption starts
    /// negative, and a derived atom must be negative there (positive in the assumption).
    fn walk(&self, formula: &'a Formula, positive: bool, exempt: bool, out: &mut Vec<String>) {
        match formula {
            Formula::Atom(atom) => self.atom(atom, positive, exempt, out),
            Formula::Not(f) => self.walk(f, !positive, exempt, out),
            Formula::And(fs) | Formula::Or(fs) => {
                fs.iter().for_each(|f| self.walk(f, positive, exempt, out))
            }
            Formula::Implies(lhs, rhs) => {
                self.walk(lhs, !positive, exempt, out);
                self.walk(rhs, positive, exempt, out);
            }
            Formula::Exists(_, f) | Formula::Forall(_, f) => self.walk(f, positive, exempt, out),
        }
    }

    fn atom(
        &self,
        atom: &'a Atom<TermVarIdx>,
        positive: bool,
        exempt: bool,
        out: &mut Vec<String>,
    ) {
        let in_guard = atom
            .guard
            .as_deref()
            .is_some_and(|guard| self.formula_mentions_with(guard, exempt));
        let in_args = atom.args.iter().any(|t| self.term_mentions_with(t, exempt));
        if in_guard || in_args {
            out.push(format!("a term or guard of `{}`", atom.pred));
        }
        match &atom.pred {
            Pred::UserDefined(pred) if self.derived.contains(pred) => {
                if positive {
                    out.push(format!("`{pred}` negated or in a premise"));
                }
            }
            Pred::UserDefined(pred) => match self.bodies.get(pred) {
                Some(body) => self.walk(body, positive, exempt, out),
                None if self.dependent.contains(pred) => {
                    out.push(format!("`{pred}`, whose definition depends on it"))
                }
                None => {}
            },
            Pred::ForallPred(pred) if !exempt => match (self.forall)(pred) {
                ForallMember::Independent => {}
                ForallMember::Derived if !positive => {}
                ForallMember::Derived => out.push(format!("`{pred}` negated or in a premise")),
                ForallMember::Dependent => {
                    out.push(format!("`{pred}`, whose instances may depend on it"))
                }
            },
            _ => {}
        }
    }

    /// Whether a member of `D` occurs anywhere in `formula`.
    fn formula_mentions(&self, formula: &Formula) -> bool {
        self.formula_mentions_with(formula, false)
    }

    fn formula_mentions_with(&self, formula: &Formula, exempt: bool) -> bool {
        formula.iter_atoms().any(|atom| {
            let pred = match &atom.pred {
                Pred::UserDefined(pred) => self.dependent.contains(pred),
                Pred::ForallPred(pred) => !exempt && self.forall_member(pred),
                _ => false,
            };
            pred || atom.args.iter().any(|t| self.term_mentions_with(t, exempt))
                || atom
                    .guard
                    .as_deref()
                    .is_some_and(|guard| self.formula_mentions_with(guard, exempt))
        })
    }

    fn term_mentions(&self, term: &Term) -> bool {
        self.term_mentions_with(term, false)
    }

    fn term_mentions_with(&self, term: &Term, exempt: bool) -> bool {
        let user = term
            .user_defined_fns()
            .into_iter()
            .any(|f| self.dependent.contains(f));
        let forall = !exempt && term.forall_fns().into_iter().any(|f| self.forall_member(f));
        user || forall
    }

    fn forall_member(&self, pred: &ForallPred) -> bool {
        (self.forall)(pred) != ForallMember::Independent
    }
}
