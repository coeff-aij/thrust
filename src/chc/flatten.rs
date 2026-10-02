//! An optimization that passes a tuple- or `Mut`-sorted argument of a loop-head predicate
//! variable as its components.
//!
//! A column of sort `(s_0, .., s_n)` becomes the columns `x.0, .., x.n` (components of a singleton
//! sort are left out), and a column of sort `Mut<s>` becomes `current x, final x`, recursively.
//! Both constructors are the only ones of their sort, so a value is determined by its components
//! and `P(x) := P'(components of x)` makes the two systems equisatisfiable. This is the
//! CHC-level counterpart of the template-level flattening (`push_flat_arg` in
//! `src/rty/template.rs`), restricted to the predicate variables that occur in the head and in
//! the body of one clause.

use super::dedup::{pred_vars_in_formulas, recursive_pred_vars};
use super::*;

fn push_components(args: &mut Vec<Term>, sig: &mut PredSig, term: Term, sort: Sort) {
    match sort {
        Sort::Tuple(sorts) => {
            for (i, s) in sorts.into_iter().enumerate() {
                if s.is_singleton() {
                    continue;
                }
                push_components(args, sig, Term::TupleProj(Box::new(term.clone()), i), s);
            }
        }
        Sort::Box(inner) => push_components(args, sig, Term::BoxCurrent(Box::new(term)), *inner),
        Sort::Mut(inner) => {
            let current = Term::MutCurrent(Box::new(term.clone()));
            push_components(args, sig, current, (*inner).clone());
            push_components(args, sig, Term::MutFinal(Box::new(term)), *inner);
        }
        sort => {
            args.push(term);
            sig.push(sort);
        }
    }
}

fn is_composite(sort: &Sort) -> bool {
    matches!(sort, Sort::Tuple(_) | Sort::Box(_) | Sort::Mut(_))
}

fn flatten_atom(atom: &mut Atom, sigs: &HashMap<PredVarId, PredSig>) {
    let Pred::Var(p) = atom.pred else {
        return;
    };
    let Some(sig) = sigs.get(&p) else {
        return;
    };
    let mut args = Vec::new();
    let mut new_sig = PredSig::new();
    for (term, sort) in std::mem::take(&mut atom.args)
        .into_iter()
        .zip(sig.iter().cloned())
    {
        push_components(&mut args, &mut new_sig, term, sort);
    }
    atom.args = args;
}

/// Splits every tuple- or `Mut`-sorted argument of the recursive predicate variables (the loop
/// heads) into its components (see the module documentation).
pub fn flatten_recursive_pred_args(mut system: System) -> System {
    let excluded = pred_vars_in_formulas(&system);
    let mut recursive: Vec<_> = recursive_pred_vars(&system)
        .into_iter()
        .filter(|p| !excluded.contains(p))
        .filter(|p| system.pred_vars[*p].sig.iter().any(is_composite))
        .collect();
    recursive.sort_by_key(|p| p.index());
    let old_sigs: HashMap<PredVarId, PredSig> = recursive
        .iter()
        .map(|p| (*p, system.pred_vars[*p].sig.clone()))
        .collect();
    for p in recursive {
        let mut placeholder = Vec::new();
        let mut sig = PredSig::new();
        for sort in old_sigs[&p].iter().cloned() {
            push_components(&mut placeholder, &mut sig, Term::Null, sort);
        }
        tracing::info!(pred = %p, from = old_sigs[&p].len(), to = sig.len(), "flatten_recursive_pred_args");
        system.pred_vars[p].sig = sig;
    }
    for clause in system.clauses.iter_mut() {
        flatten_atom(&mut clause.head, &old_sigs);
        for atom in &mut clause.body.atoms {
            flatten_atom(atom, &old_sigs);
        }
    }
    system
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clause(vars: Vec<Sort>, head: Atom, body: Body) -> Clause {
        let sort = vars.first().cloned().unwrap_or_else(Sort::int);
        Clause {
            origin: debug::origin::ClauseOrigin {
                environment: Vec::new(),
                body: Vec::new(),
                head: debug::origin::Entry::parameter(TermVarIdx::from(0usize), &sort),
            },
            vars: vars.into_iter().collect(),
            head,
            body,
            debug_info: DebugInfo::default(),
        }
    }

    fn v(i: usize) -> Term {
        Term::var(i.into())
    }

    #[test]
    fn splits_the_tuple_argument_of_a_loop_head_only() {
        let pair = Sort::tuple(vec![Sort::int(), Sort::mut_(Sort::int())]);
        let mut system = System::default();
        let p = system.new_pred_var(vec![pair.clone()], DebugInfo::default());
        let q = system.new_pred_var(vec![pair.clone()], DebugInfo::default());
        // Q(t) => P(t); P(t) => P(t); P(t) => Q(t)
        system.push_clause(clause(
            vec![pair.clone()],
            Atom::new(Pred::Var(p), vec![v(0)]),
            Body::new(vec![Atom::new(Pred::Var(q), vec![v(0)])], Formula::top()),
        ));
        system.push_clause(clause(
            vec![pair.clone()],
            Atom::new(Pred::Var(p), vec![v(0)]),
            Body::new(vec![Atom::new(Pred::Var(p), vec![v(0)])], Formula::top()),
        ));
        let system = flatten_recursive_pred_args(system);
        assert_eq!(
            system.pred_vars[p].sig,
            vec![Sort::int(), Sort::int(), Sort::int()]
        );
        assert_eq!(system.pred_vars[q].sig, vec![pair]);
        let head = &system.clauses.iter().next().unwrap().head;
        let t = || Box::new(v(0));
        assert_eq!(
            head.args,
            vec![
                Term::TupleProj(t(), 0),
                Term::MutCurrent(Box::new(Term::TupleProj(t(), 1))),
                Term::MutFinal(Box::new(Term::TupleProj(t(), 1))),
            ]
        );
    }
}
