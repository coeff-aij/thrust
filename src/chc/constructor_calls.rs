//! Expansion of the calls a definition makes on a constructor (see [`expand_calls_on_constructors`]).

use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;

use super::candidate_atoms::{map_formula_terms, simplify_term};
use super::{
    Atom, Datatype, DatatypeSymbol, Formula, Pred, System, Term, UserDefinedPred,
    UserDefinedPredBody, UserQuantifiedVarId,
};

/// The system with each definition's calls on a constructor expanded: a call to another defined
/// predicate that has a `Mut` or a tuple constructor among its arguments is replaced by the
/// callee's body. Every selector or discriminant applied to a constructor in a definition is then
/// reduced, as `(mut_current (mut a b))` to `a`.
///
/// A reader that expands each definition into its callers by substitution, without reducing,
/// copies such an argument at every use of the parameter. When a definition passes the parts of
/// its parameter to the next one in a constructor, as `completed` of nested iterator adapters
/// does, the copies double at each level. Expanded and reduced here, each definition grows only
/// by its callee's body. A call is kept when the callee binds a quantified variable that the
/// arguments name or that is bound around the call, so that no variable is captured or shadowed.
/// Recursive, opaque and derived predicates and logic functions are never expanded.
pub fn expand_calls_on_constructors(mut system: System) -> System {
    let discriminants = discriminants(&system.datatypes);
    let opaque = system.opaque_preds.clone();
    let mut callees: HashMap<UserDefinedPred, Callee> = HashMap::new();
    for i in dependency_order(&system) {
        let def = &mut system.user_defined_pred_defs[i];
        let UserDefinedPredBody::Formula(body) = &mut def.body else {
            continue;
        };
        let expansion = Expansion {
            callees: &callees,
            discriminants: &discriminants,
        };
        let expanded = expansion.formula(expansion.reduce(std::mem::take(body)), &mut Vec::new());
        *body = expanded.clone();
        if def.is_recursive() || opaque.contains(&def.symbol) {
            continue;
        }
        callees.insert(def.symbol.clone(), Callee::new(def.sig.len(), expanded));
    }
    system
}

/// The indices of the definitions, each after the definitions it calls.
fn dependency_order(system: &System) -> Vec<usize> {
    let mut seen = HashSet::new();
    let mut order = Vec::new();
    for def in system.user_defined_preds_in_dependency_order() {
        if !seen.insert(&def.symbol) {
            continue;
        }
        order.extend(
            (0..system.user_defined_pred_defs.len())
                .filter(|&i| system.user_defined_pred_defs[i].symbol == def.symbol),
        );
    }
    order
}

fn discriminants(datatypes: &[Datatype]) -> HashMap<DatatypeSymbol, BigInt> {
    datatypes
        .iter()
        .flat_map(|d| &d.ctors)
        .map(|c| (c.symbol.clone(), c.discriminant.clone()))
        .collect()
}

struct Callee {
    arity: usize,
    body: Formula,
    /// The quantified variables named in the body, all bound there.
    binders: HashSet<UserQuantifiedVarId>,
}

impl Callee {
    fn new(arity: usize, body: Formula) -> Self {
        let mut binders = HashSet::new();
        quantified_vars_in_formula(&body, &mut binders);
        Callee {
            arity,
            body,
            binders,
        }
    }
}

struct Expansion<'a> {
    callees: &'a HashMap<UserDefinedPred, Callee>,
    discriminants: &'a HashMap<DatatypeSymbol, BigInt>,
}

impl Expansion<'_> {
    /// `formula` with its calls on constructors expanded; `bound` holds the quantified variables
    /// bound around it.
    fn formula(&self, formula: Formula, bound: &mut Vec<UserQuantifiedVarId>) -> Formula {
        match formula {
            Formula::Atom(atom) => self.atom(atom, bound),
            Formula::Not(fo) => Formula::Not(Box::new(self.formula(*fo, bound))),
            Formula::And(fs) => {
                Formula::And(fs.into_iter().map(|fo| self.formula(fo, bound)).collect())
            }
            Formula::Or(fs) => {
                Formula::Or(fs.into_iter().map(|fo| self.formula(fo, bound)).collect())
            }
            Formula::Implies(lhs, rhs) => {
                let lhs = self.formula(*lhs, bound);
                Formula::Implies(Box::new(lhs), Box::new(self.formula(*rhs, bound)))
            }
            Formula::Exists(vars, fo) => {
                let fo = self.under_binders(&vars, *fo, bound);
                Formula::Exists(vars, Box::new(fo))
            }
            Formula::Forall(vars, fo) => {
                let fo = self.under_binders(&vars, *fo, bound);
                Formula::Forall(vars, Box::new(fo))
            }
        }
    }

    fn under_binders<S>(
        &self,
        vars: &[(UserQuantifiedVarId, S)],
        formula: Formula,
        bound: &mut Vec<UserQuantifiedVarId>,
    ) -> Formula {
        let depth = bound.len();
        bound.extend(vars.iter().map(|(v, _)| *v));
        let formula = self.formula(formula, bound);
        bound.truncate(depth);
        formula
    }

    fn atom(&self, atom: Atom, bound: &mut Vec<UserQuantifiedVarId>) -> Formula {
        let Some(callee) = self.expandable_callee(&atom, bound) else {
            return Formula::Atom(atom);
        };
        let Atom { guard, args, .. } = atom;
        assert_eq!(
            args.len(),
            callee.arity,
            "a call takes the callee's parameters"
        );
        let body = callee.body.clone().subst_var(|v| args[v.index()].clone());
        let body = self.formula(self.reduce(body), bound);
        match guard {
            Some(guard) => Formula::Implies(guard, Box::new(body)),
            None => body,
        }
    }

    fn expandable_callee(&self, atom: &Atom, bound: &[UserQuantifiedVarId]) -> Option<&Callee> {
        let Pred::UserDefined(symbol) = &atom.pred else {
            return None;
        };
        let callee = self.callees.get(symbol)?;
        if !atom.args.iter().any(is_constructor) {
            return None;
        }
        let mut named = bound.iter().copied().collect::<HashSet<_>>();
        atom.args
            .iter()
            .for_each(|t| quantified_vars_in_term(t, &mut named));
        named.is_disjoint(&callee.binders).then_some(callee)
    }

    fn reduce(&self, formula: Formula) -> Formula {
        map_formula_terms(formula, &mut |t| match simplify_term(t) {
            Term::DatatypeDiscr(sym, t) => match *t {
                Term::DatatypeCtor(_, ref ctor, _) if self.discriminants.contains_key(ctor) => {
                    Term::Int(self.discriminants[ctor].clone())
                }
                t => Term::DatatypeDiscr(sym, Box::new(t)),
            },
            t => t,
        })
    }
}

/// Whether `term` builds a value whose parts a definition reads with selectors Thrust reduces.
fn is_constructor(term: &Term) -> bool {
    matches!(term, Term::Mut(..) | Term::Tuple(_))
}

fn quantified_vars_in_formula(formula: &Formula, out: &mut HashSet<UserQuantifiedVarId>) {
    match formula {
        Formula::Atom(atom) => {
            if let Some(guard) = &atom.guard {
                quantified_vars_in_formula(guard, out);
            }
            atom.args
                .iter()
                .for_each(|t| quantified_vars_in_term(t, out));
        }
        Formula::Not(fo) => quantified_vars_in_formula(fo, out),
        Formula::And(fs) | Formula::Or(fs) => {
            fs.iter().for_each(|fo| quantified_vars_in_formula(fo, out))
        }
        Formula::Implies(lhs, rhs) => {
            quantified_vars_in_formula(lhs, out);
            quantified_vars_in_formula(rhs, out);
        }
        Formula::Exists(vars, fo) | Formula::Forall(vars, fo) => {
            out.extend(vars.iter().map(|(v, _)| *v));
            quantified_vars_in_formula(fo, out);
        }
    }
}

fn quantified_vars_in_term(term: &Term, out: &mut HashSet<UserQuantifiedVarId>) {
    for t in term.preorder() {
        match t {
            Term::UserQuantifiedVar(_, v) | Term::ArrayLambda(v, _, _) => {
                out.insert(*v);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_index::IndexVec;

    use super::super::{Sort, TermVarIdx};
    use super::*;

    fn v(i: usize) -> Term {
        Term::var(i.into())
    }

    fn call(symbol: &UserDefinedPred, args: Vec<Term>) -> Formula {
        Formula::Atom(Atom::new(Pred::UserDefined(symbol.clone()), args))
    }

    fn body_of<'a>(system: &'a System, symbol: &UserDefinedPred) -> &'a Formula {
        let def = system
            .user_defined_pred_defs
            .iter()
            .find(|d| &d.symbol == symbol)
            .unwrap();
        let UserDefinedPredBody::Formula(body) = &def.body else {
            panic!("a formula body");
        };
        body
    }

    /// `q(m) := *m = °m` and `p(m) := q(<(*m).0, (°m).0>)` over `m: Mut<(Int, Int)>`, with `p`'s
    /// argument to `q` given by `arg`.
    fn system_with_caller(arg: impl FnOnce() -> Term) -> (System, UserDefinedPred) {
        let mut system = System::default();
        let q = UserDefinedPred::new("q".to_owned());
        let p = UserDefinedPred::new("p".to_owned());
        let int_mut: IndexVec<TermVarIdx, Sort> = [Sort::mut_(Sort::int())].into_iter().collect();
        let pair = Sort::tuple(vec![Sort::int(), Sort::int()]);
        let pair_mut: IndexVec<TermVarIdx, Sort> = [Sort::mut_(pair)].into_iter().collect();
        let q_body = Formula::Atom(v(0).mut_current().equal_to(v(0).mut_final()));
        system.push_pred_define_formula(q.clone(), int_mut, q_body);
        system.push_pred_define_formula(p.clone(), pair_mut, call(&q, vec![arg()]));
        (system, p)
    }

    #[test]
    fn expands_a_call_on_a_mut_and_reduces_its_selectors() {
        let arg = || {
            Term::mut_(
                Term::TupleProj(Box::new(v(0).mut_current()), 0),
                Term::TupleProj(Box::new(v(0).mut_final()), 0),
            )
        };
        let (system, p) = system_with_caller(arg);
        let system = expand_calls_on_constructors(system);
        let expected = Term::TupleProj(Box::new(v(0).mut_current()), 0)
            .equal_to(Term::TupleProj(Box::new(v(0).mut_final()), 0));
        assert_eq!(body_of(&system, &p), &Formula::Atom(expected));
    }

    #[test]
    fn keeps_a_call_on_a_parameter() {
        let (system, p) = system_with_caller(|| v(0));
        let before = body_of(&system, &p).clone();
        let system = expand_calls_on_constructors(system);
        assert_eq!(body_of(&system, &p), &before);
    }

    #[test]
    fn keeps_a_call_whose_argument_names_a_variable_the_callee_binds() {
        let mut system = System::default();
        let x = system.new_user_quantified_var();
        let q = UserDefinedPred::new("q".to_owned());
        let p = UserDefinedPred::new("p".to_owned());
        let int_mut: IndexVec<TermVarIdx, Sort> = [Sort::mut_(Sort::int())].into_iter().collect();
        let ints: IndexVec<TermVarIdx, Sort> = [Sort::int()].into_iter().collect();
        let bound = || Term::UserQuantifiedVar(Sort::int(), x);
        // q(m) := ∃x. x = *m, p(n) := ∃x. q(<x, n>)
        let q_body = Formula::exists(
            vec![(x, Sort::int())],
            Formula::Atom(bound().equal_to(v(0).mut_current())),
        );
        let p_body = Formula::exists(
            vec![(x, Sort::int())],
            call(&q, vec![Term::mut_(bound(), v(0))]),
        );
        system.push_pred_define_formula(q, int_mut, q_body);
        system.push_pred_define_formula(p.clone(), ints, p_body.clone());
        let system = expand_calls_on_constructors(system);
        assert_eq!(body_of(&system, &p), &p_body);
    }
}
