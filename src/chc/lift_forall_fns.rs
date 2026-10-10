//! Passing the forall functions a user-defined function applies to it as array arguments.
//!
//! A forall function of one argument is an array-sorted term in PCSat's logic. PCSat (fptprove
//! a27680b5c) cannot read a `define-fun-rec` whose body applies one: its recursive-function
//! encoding fails on the unbound symbol, and with that encoding off it answers `unsat` for
//! valid clauses. So a
//! definition takes each forall function its body reaches, directly or through the definitions
//! it calls, as an array parameter, which its body `select`s and passes on, and every other
//! call passes the forall function itself.

use std::collections::HashMap;

use super::candidate_atoms::map_term;
use super::*;

pub fn lift_forall_fns(mut system: System) -> System {
    let lifted = lifted_forall_fns(&system.user_defined_pred_defs);
    if lifted.values().all(Vec::is_empty) {
        return system;
    }
    for def in &mut system.user_defined_pred_defs {
        lift_def(def, &lifted);
    }
    let bare = |pred: &ForallPred| Term::ForallFn(pred.clone(), Vec::new());
    let pass = Pass {
        lifted: &lifted,
        reference: &bare,
        select: None,
    };
    system.clauses = std::mem::take(&mut system.clauses)
        .into_iter()
        .map(|clause| Clause {
            head: pass.atom(clause.head),
            body: Body {
                atoms: clause
                    .body
                    .atoms
                    .into_iter()
                    .map(|atom| pass.atom(atom))
                    .collect(),
                formula: pass.formula(clause.body.formula),
            },
            ..clause
        })
        .collect();
    for laws in system.laws.values_mut() {
        for law in laws {
            *law = pass.formula(std::mem::take(law));
        }
    }
    for candidates in &mut system.candidate_atoms {
        for atom in &mut candidates.atoms {
            *atom = pass.formula(std::mem::take(atom));
        }
    }
    system
}

/// Rewrites calls to pass on the forall functions their callee reaches, as `reference` names
/// them, and with `select`, applications of those forall functions into `select`s.
struct Pass<'a> {
    lifted: &'a HashMap<UserDefinedPred, Vec<ForallPred>>,
    reference: &'a dyn Fn(&ForallPred) -> Term,
    select: Option<&'a [ForallPred]>,
}

impl Pass<'_> {
    fn extra_args(&self, symbol: &UserDefinedPred) -> Vec<Term> {
        self.lifted
            .get(symbol)
            .into_iter()
            .flatten()
            .map(|pred| (self.reference)(pred))
            .collect()
    }

    fn term(&self, term: Term) -> Term {
        map_term(term, &mut |term| match term {
            Term::ForallFn(pred, mut args)
                if args.len() == 1 && self.select.is_some_and(|own| own.contains(&pred)) =>
            {
                Term::App(
                    Function::SELECT,
                    vec![(self.reference)(&pred), args.remove(0)],
                )
            }
            Term::UserDefinedFn(symbol, sort, mut args) => {
                args.extend(self.extra_args(&symbol));
                Term::UserDefinedFn(symbol, sort, args)
            }
            term => term,
        })
    }

    fn atom(&self, atom: Atom) -> Atom {
        let mut atom = atom;
        atom.guard = atom.guard.map(|guard| Box::new(self.formula(*guard)));
        atom.args = std::mem::take(&mut atom.args)
            .into_iter()
            .map(|term| self.term(term))
            .collect();
        if let Pred::UserDefined(symbol) = &atom.pred {
            let extra = self.extra_args(symbol);
            atom.args.extend(extra);
        }
        atom
    }

    fn formula(&self, formula: Formula) -> Formula {
        match formula {
            Formula::Atom(atom) => Formula::Atom(self.atom(atom)),
            Formula::Not(fo) => Formula::Not(Box::new(self.formula(*fo))),
            Formula::And(fs) => Formula::And(fs.into_iter().map(|fo| self.formula(fo)).collect()),
            Formula::Or(fs) => Formula::Or(fs.into_iter().map(|fo| self.formula(fo)).collect()),
            Formula::Implies(lhs, rhs) => {
                Formula::Implies(Box::new(self.formula(*lhs)), Box::new(self.formula(*rhs)))
            }
            Formula::Exists(vars, fo) => Formula::Exists(vars, Box::new(self.formula(*fo))),
            Formula::Forall(vars, fo) => Formula::Forall(vars, Box::new(self.formula(*fo))),
        }
    }
}

/// The forall functions of one argument each definition reaches, in a fixed order.
fn lifted_forall_fns(defs: &[UserDefinedPredDef]) -> HashMap<UserDefinedPred, Vec<ForallPred>> {
    let mut lifted: HashMap<UserDefinedPred, Vec<ForallPred>> = defs
        .iter()
        .map(|def| (def.symbol.clone(), direct_forall_fns(def)))
        .collect();
    loop {
        let mut changed = false;
        for def in defs {
            let mut reached = lifted[&def.symbol].clone();
            for callee in def.callees() {
                for pred in lifted.get(callee).into_iter().flatten() {
                    if !reached.contains(pred) {
                        reached.push(pred.clone());
                    }
                }
            }
            if reached.len() != lifted[&def.symbol].len() {
                reached.sort();
                lifted.insert(def.symbol.clone(), reached);
                changed = true;
            }
        }
        if !changed {
            return lifted;
        }
    }
}

fn direct_forall_fns(def: &UserDefinedPredDef) -> Vec<ForallPred> {
    let terms: Vec<&Term> = match &def.body {
        UserDefinedPredBody::Raw(_) => Vec::new(),
        UserDefinedPredBody::Term(_, term) => vec![term],
        UserDefinedPredBody::Formula(formula) => {
            formula.iter_atoms().flat_map(|atom| &atom.args).collect()
        }
    };
    let mut preds: Vec<ForallPred> = terms
        .into_iter()
        .flat_map(Term::forall_fns)
        .filter(|pred| pred.params.len() == 1)
        .cloned()
        .collect();
    preds.sort();
    preds.dedup();
    preds
}

/// Gives `def` a parameter for each forall function it reaches and reads them through those.
fn lift_def(def: &mut UserDefinedPredDef, lifted: &HashMap<UserDefinedPred, Vec<ForallPred>>) {
    let own = lifted[&def.symbol].clone();
    let arity = def.sig.len();
    for (idx, pred) in own.iter().enumerate() {
        let sort = Sort::array(pred.params[0].clone(), pred.result.clone());
        def.sig
            .push((TermVarIdx::from(arity + idx).to_string(), sort));
    }
    let param = |pred: &ForallPred| {
        let idx = own.iter().position(|p| p == pred).unwrap();
        Term::var(TermVarIdx::from(arity + idx))
    };
    let pass = Pass {
        lifted,
        reference: &param,
        select: Some(&own),
    };
    def.body = match std::mem::replace(&mut def.body, UserDefinedPredBody::Raw(String::new())) {
        UserDefinedPredBody::Term(sort, term) => UserDefinedPredBody::Term(sort, pass.term(term)),
        UserDefinedPredBody::Formula(formula) => {
            UserDefinedPredBody::Formula(pass.formula(formula))
        }
        raw => raw,
    };
}
