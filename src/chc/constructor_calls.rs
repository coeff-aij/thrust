//! Definitions that pass the parts of a constructor instead of the constructor (see
//! [`pass_constructor_parts`]).

use std::collections::{HashMap, HashSet};

use num_bigint::BigInt;

use super::candidate_atoms::{map_formula_terms, simplify_term};
use super::{
    Atom, Datatype, DatatypeSymbol, Formula, Pred, Sort, System, Term, TermVarIdx, UserDefinedPred,
    UserDefinedPredBody, UserDefinedPredDef, UserDefinedPredSig,
};

/// The system with each call that a definition makes on a constructor replaced by a call on the
/// constructor's parts. A call to another defined predicate that has a `Mut` or tuple
/// constructor among its arguments becomes a call to a copy of the callee that takes the parts
/// as parameters, `q(mut a b)` to `q_parts_mpp(a, b)`. The copy's body is the callee's with the
/// parameter replaced by the constructor of the new parameters. Every selector or discriminant
/// applied to a constructor in a definition is then reduced, as `(mut_current (mut a b))` to `a`.
///
/// A reader that expands each definition into its callers by substitution, without reducing,
/// copies a constructor argument at every use of the parameter. When a definition passes the
/// parts of its parameter to the next one in a constructor, as `completed` of nested iterator
/// adapters does, the argument names the caller's parameter twice, and the copies double at each
/// level; a part names it once. One copy is made per callee and shape of the arguments, so the
/// query grows by at most one definition per call. Recursive, opaque and derived predicates and
/// logic functions are not copied, and clauses are left as they are.
pub fn pass_constructor_parts(mut system: System) -> System {
    let mut copies = Copies {
        callees: HashMap::new(),
        made: HashMap::new(),
        defs: Vec::new(),
        discriminants: discriminants(&system.datatypes),
    };
    let opaque = system.opaque_preds.clone();
    for i in dependency_order(&system) {
        let def = &mut system.user_defined_pred_defs[i];
        let UserDefinedPredBody::Formula(body) = &mut def.body else {
            continue;
        };
        let rewritten = copies.formula(copies.reduce(std::mem::take(body)));
        *body = rewritten.clone();
        if def.is_recursive() || opaque.contains(&def.symbol) {
            continue;
        }
        copies
            .callees
            .insert(def.symbol.clone(), (def.sig.clone(), rewritten));
    }
    system.user_defined_pred_defs.extend(copies.defs);
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

/// How an argument is built from the constructors whose selectors Thrust reduces; a `Part` is
/// passed as it is.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Shape {
    Part,
    Mut(Box<Shape>, Box<Shape>),
    Tuple(Vec<Shape>),
}

impl Shape {
    /// The shape of `term`, an argument for a parameter of `sort`.
    fn of(term: &Term, sort: &Sort) -> Shape {
        match (term, sort) {
            (Term::Mut(current, final_), Sort::Mut(inner)) => Shape::Mut(
                Box::new(Shape::of(current, inner)),
                Box::new(Shape::of(final_, inner)),
            ),
            (Term::Tuple(ts), Sort::Tuple(sorts)) if ts.len() == sorts.len() => {
                Shape::Tuple(ts.iter().zip(sorts).map(|(t, s)| Shape::of(t, s)).collect())
            }
            _ => Shape::Part,
        }
    }

    /// Pushes the parts of `term`, an argument of this shape, in order.
    fn parts(&self, term: Term, out: &mut Vec<Term>) {
        match (self, term) {
            (Shape::Mut(current, final_), Term::Mut(c, f)) => {
                current.parts(*c, out);
                final_.parts(*f, out);
            }
            (Shape::Tuple(shapes), Term::Tuple(ts)) => {
                for (shape, t) in shapes.iter().zip(ts) {
                    shape.parts(t, out);
                }
            }
            (_, term) => out.push(term),
        }
    }

    /// The constructor of this shape over new parameters, whose sorts are pushed onto `params`
    /// in the order of [`Shape::parts`].
    fn build(&self, sort: &Sort, params: &mut Vec<Sort>) -> Term {
        match (self, sort) {
            (Shape::Mut(current, final_), Sort::Mut(inner)) => {
                let current = current.build(inner, params);
                Term::mut_(current, final_.build(inner, params))
            }
            (Shape::Tuple(shapes), Sort::Tuple(sorts)) => Term::Tuple(
                shapes
                    .iter()
                    .zip(sorts)
                    .map(|(shape, s)| shape.build(s, params))
                    .collect(),
            ),
            _ => {
                params.push(sort.clone());
                Term::var(TermVarIdx::from_usize(params.len() - 1))
            }
        }
    }

    /// The shape's name in its copy's symbol, a prefix code: `p` a part, `m` a `Mut` of two
    /// shapes, `t<n>_` a tuple of n.
    fn code(&self) -> String {
        match self {
            Shape::Part => "p".to_owned(),
            Shape::Mut(current, final_) => format!("m{}{}", current.code(), final_.code()),
            Shape::Tuple(shapes) => {
                let inner: String = shapes.iter().map(Shape::code).collect();
                format!("t{}_{inner}", shapes.len())
            }
        }
    }
}

struct Copies {
    /// The definitions a copy can be made of, with their signatures and rewritten bodies.
    callees: HashMap<UserDefinedPred, (UserDefinedPredSig, Formula)>,
    made: HashMap<(UserDefinedPred, Vec<Shape>), UserDefinedPred>,
    defs: Vec<UserDefinedPredDef>,
    discriminants: HashMap<DatatypeSymbol, BigInt>,
}

impl Copies {
    fn formula(&mut self, formula: Formula) -> Formula {
        match formula {
            Formula::Atom(atom) => Formula::Atom(self.atom(atom)),
            Formula::Not(fo) => Formula::Not(Box::new(self.formula(*fo))),
            Formula::And(fs) => Formula::And(fs.into_iter().map(|fo| self.formula(fo)).collect()),
            Formula::Or(fs) => Formula::Or(fs.into_iter().map(|fo| self.formula(fo)).collect()),
            Formula::Implies(lhs, rhs) => {
                let lhs = self.formula(*lhs);
                Formula::Implies(Box::new(lhs), Box::new(self.formula(*rhs)))
            }
            Formula::Exists(vars, fo) => Formula::Exists(vars, Box::new(self.formula(*fo))),
            Formula::Forall(vars, fo) => Formula::Forall(vars, Box::new(self.formula(*fo))),
        }
    }

    fn atom(&mut self, atom: Atom) -> Atom {
        let Atom { guard, pred, args } = atom;
        let guard = guard.map(|g| Box::new(self.formula(*g)));
        let Some((callee, shapes)) = self.call_on_constructor(&pred, &args) else {
            return Atom { guard, pred, args };
        };
        let symbol = self.copy(&callee, shapes.clone());
        let mut parts = Vec::new();
        for (shape, arg) in shapes.iter().zip(args) {
            shape.parts(arg, &mut parts);
        }
        Atom {
            guard,
            pred: Pred::UserDefined(symbol),
            args: parts,
        }
    }

    /// The callee and the shapes of the arguments, when `pred` is a definition a copy can be made
    /// of and an argument is a constructor.
    fn call_on_constructor(
        &self,
        pred: &Pred,
        args: &[Term],
    ) -> Option<(UserDefinedPred, Vec<Shape>)> {
        let Pred::UserDefined(callee) = pred else {
            return None;
        };
        let (sig, _) = self.callees.get(callee)?;
        let shapes: Vec<Shape> = args
            .iter()
            .zip(sig)
            .map(|(t, (_, sort))| Shape::of(t, sort))
            .collect();
        let on_constructor = shapes.iter().any(|s| *s != Shape::Part);
        on_constructor.then(|| (callee.clone(), shapes))
    }

    /// The copy of `callee` that takes the parts of arguments of `shapes`, made once.
    fn copy(&mut self, callee: &UserDefinedPred, shapes: Vec<Shape>) -> UserDefinedPred {
        let key = (callee.clone(), shapes);
        if let Some(symbol) = self.made.get(&key) {
            return symbol.clone();
        }
        let (sig, body) = self.callees[callee].clone();
        let mut params = Vec::new();
        let args: Vec<Term> = sig
            .iter()
            .zip(&key.1)
            .map(|((_, sort), shape)| shape.build(sort, &mut params))
            .collect();
        let body = body.subst_var(|v| args[v.index()].clone());
        let body = self.formula(self.reduce(body));
        let code: String = key.1.iter().map(Shape::code).collect();
        let symbol = UserDefinedPred {
            inner: format!("{}_parts_{code}", callee.inner),
            name: callee.name.as_ref().map(|name| format!("{name} (parts)")),
            ..callee.clone()
        };
        self.defs.push(UserDefinedPredDef {
            symbol: symbol.clone(),
            sig: params
                .into_iter()
                .enumerate()
                .map(|(i, sort)| (TermVarIdx::from_usize(i).to_string(), sort))
                .collect(),
            body: UserDefinedPredBody::Formula(body),
            sort_subst: Vec::new(),
            dependencies: HashSet::new(),
            decreases: None,
        });
        self.made.insert(key, symbol.clone());
        symbol
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

#[cfg(test)]
mod tests {
    use rustc_index::IndexVec;

    use super::*;

    fn v(i: usize) -> Term {
        Term::var(i.into())
    }

    fn call(symbol: &UserDefinedPred, args: Vec<Term>) -> Formula {
        Formula::Atom(Atom::new(Pred::UserDefined(symbol.clone()), args))
    }

    fn def_of<'a>(system: &'a System, symbol: &UserDefinedPred) -> &'a UserDefinedPredDef {
        system
            .user_defined_pred_defs
            .iter()
            .find(|d| &d.symbol == symbol)
            .unwrap()
    }

    fn body_of<'a>(system: &'a System, symbol: &UserDefinedPred) -> &'a Formula {
        let UserDefinedPredBody::Formula(body) = &def_of(system, symbol).body else {
            panic!("a formula body");
        };
        body
    }

    /// `q(m) := *m = °m` over `m: Mut<Int>`, and `p(m, n) := body` over `m: Mut<(Int, Int)>` and
    /// `n: Mut<Int>`.
    fn system_with_caller(body: impl FnOnce(&UserDefinedPred) -> Formula) -> System {
        let mut system = System::default();
        let q = UserDefinedPred::new("q".to_owned());
        let int_mut: IndexVec<TermVarIdx, Sort> = [Sort::mut_(Sort::int())].into_iter().collect();
        let pair = Sort::tuple(vec![Sort::int(), Sort::int()]);
        let p_params: IndexVec<TermVarIdx, Sort> = [Sort::mut_(pair), Sort::mut_(Sort::int())]
            .into_iter()
            .collect();
        let q_body = Formula::Atom(v(0).mut_current().equal_to(v(0).mut_final()));
        let p_body = body(&q);
        system.push_pred_define_formula(q, int_mut, q_body);
        system.push_pred_define_formula(UserDefinedPred::new("p".to_owned()), p_params, p_body);
        system
    }

    #[test]
    fn passes_the_parts_of_a_mut_to_one_copy_per_shape() {
        let first = || Term::TupleProj(Box::new(v(0).mut_current()), 0);
        let second = || Term::TupleProj(Box::new(v(0).mut_final()), 1);
        let system = system_with_caller(|q| {
            call(q, vec![Term::mut_(first(), second())])
                .and(call(q, vec![Term::mut_(second(), first())]))
        });
        let system = pass_constructor_parts(system);
        let copy = UserDefinedPred::new("q_parts_mpp".to_owned());
        let p = UserDefinedPred::new("p".to_owned());
        assert_eq!(system.user_defined_pred_defs.len(), 3);
        assert_eq!(
            body_of(&system, &p),
            &call(&copy, vec![first(), second()]).and(call(&copy, vec![second(), first()]))
        );
        assert_eq!(body_of(&system, &copy), &Formula::Atom(v(0).equal_to(v(1))));
        assert_eq!(
            def_of(&system, &copy).sig,
            vec![
                ("v0".to_owned(), Sort::int()),
                ("v1".to_owned(), Sort::int())
            ]
        );
    }

    #[test]
    fn keeps_a_call_on_a_parameter() {
        let system = system_with_caller(|q| call(q, vec![v(1)]));
        let before = system.user_defined_pred_defs.clone();
        let system = pass_constructor_parts(system);
        assert_eq!(system.user_defined_pred_defs.len(), before.len());
        let p = UserDefinedPred::new("p".to_owned());
        assert_eq!(
            body_of(&system, &p),
            &call(&UserDefinedPred::new("q".to_owned()), vec![v(1)])
        );
    }
}
