//! An optimization that passes a tuple-, `Box`- or `Mut`-sorted argument of a loop-head
//! predicate variable as its components.
//!
//! A column of sort `(s_0, .., s_n)` becomes the columns `x.0, .., x.n` (components of a singleton
//! sort are left out), a column of sort `Box<s>` the column `*x`, and a column of sort `Mut<s>`
//! the columns `current x, final x`, recursively. Each of these constructors is the only one of
//! its sort, so a value is determined by its components and `P(x) := P'(components of x)` makes
//! the two systems equisatisfiable. Only the predicate variables that occur in the head and in
//! the body of one clause (the loop heads) are flattened.

use super::dedup::{pred_vars_in_formulas, recursive_pred_vars};
use super::*;

/// The components `term` of `sort` is split into, each with its sort, in column order.
pub(super) fn components(term: Term, sort: Sort) -> Vec<(Term, Sort)> {
    match sort {
        Sort::Tuple(sorts) => sorts
            .into_iter()
            .enumerate()
            .filter(|(_, s)| !s.is_singleton())
            .flat_map(|(i, s)| components(Term::TupleProj(Box::new(term.clone()), i), s))
            .collect(),
        Sort::Box(inner) => components(Term::BoxCurrent(Box::new(term)), *inner),
        Sort::Mut(inner) => {
            let mut parts = components(Term::MutCurrent(Box::new(term.clone())), (*inner).clone());
            parts.extend(components(Term::MutFinal(Box::new(term)), *inner));
            parts
        }
        sort => vec![(term, sort)],
    }
}

/// The term over the flattened columns, taken from `next` on in `components`'s order, that an
/// old column of `sort` equals; `None` when a left-out component has no value to write.
fn rebuild(sort: &Sort, next: &mut usize) -> Option<Term> {
    match sort {
        Sort::Tuple(sorts) => {
            let fields = sorts
                .iter()
                .map(|s| {
                    if s.is_singleton() {
                        singleton_value(s)
                    } else {
                        rebuild(s, next)
                    }
                })
                .collect::<Option<_>>()?;
            Some(Term::tuple(fields))
        }
        Sort::Box(inner) => Some(Term::box_(rebuild(inner, next)?)),
        Sort::Mut(inner) => {
            let current = rebuild(inner, next)?;
            Some(Term::mut_(current, rebuild(inner, next)?))
        }
        _ => {
            let column = Term::var(TermVarIdx::from_usize(*next));
            *next += 1;
            Some(column)
        }
    }
}

/// The one value of a singleton sort, if it can be written.
fn singleton_value(sort: &Sort) -> Option<Term> {
    match sort {
        Sort::Null => Some(Term::Null),
        Sort::Tuple(sorts) => Some(Term::tuple(
            sorts.iter().map(singleton_value).collect::<Option<_>>()?,
        )),
        Sort::Box(inner) => Some(Term::box_(singleton_value(inner)?)),
        Sort::Mut(inner) => Some(Term::mut_(singleton_value(inner)?, singleton_value(inner)?)),
        _ => None,
    }
}

fn is_composite(sort: &Sort) -> bool {
    matches!(sort, Sort::Tuple(_) | Sort::Box(_) | Sort::Mut(_))
}

fn flatten_atom(atom: &mut Atom, old_sigs: &HashMap<PredVarId, PredSig>) {
    let Pred::Var(p) = atom.pred else {
        return;
    };
    let Some(sig) = old_sigs.get(&p) else {
        return;
    };
    let args = std::mem::take(&mut atom.args);
    atom.args = args
        .into_iter()
        .zip(sig.iter().cloned())
        .flat_map(|(term, sort)| components(term, sort))
        .map(|(term, _)| term)
        .collect();
}

/// Moves the candidate atoms of a flattened predicate variable onto its new columns.
fn flatten_candidate_atoms(candidates: &mut CandidateAtoms, sig: &PredSig) {
    let mut next = 0;
    let columns: Vec<Option<Term>> = sig.iter().map(|s| rebuild(s, &mut next)).collect();
    let atoms = std::mem::take(&mut candidates.atoms);
    candidates.atoms = candidate_atoms::rewrite_atoms(atoms, |v| columns[v.index()].clone());
}

/// Splits every tuple-, `Box`- or `Mut`-sorted argument of the recursive predicate variables (the
/// loop heads) into its components (see the module documentation).
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
        let sig: PredSig = old_sigs[&p]
            .iter()
            .cloned()
            .flat_map(|sort| components(Term::Null, sort))
            .map(|(_, sort)| sort)
            .collect();
        tracing::info!(pred = %p, from = old_sigs[&p].len(), to = sig.len(), "flatten_recursive_pred_args");
        system.pred_vars[p].sig = sig;
    }
    for clause in system.clauses.iter_mut() {
        flatten_atom(&mut clause.head, &old_sigs);
        for atom in &mut clause.body.atoms {
            flatten_atom(atom, &old_sigs);
        }
    }
    for candidates in system.candidate_atoms.iter_mut() {
        if let Some(sig) = old_sigs.get(&candidates.pred) {
            flatten_candidate_atoms(candidates, sig);
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

    #[test]
    fn moves_candidate_atoms_onto_the_components() {
        let pair = Sort::tuple(vec![Sort::int(), Sort::mut_(Sort::int())]);
        let mut system = System::default();
        let p = system.new_pred_var(vec![pair.clone()], DebugInfo::default());
        // P(t) => P(t), with the candidate t.0 = current t.1
        system.push_clause(clause(
            vec![pair],
            Atom::new(Pred::Var(p), vec![v(0)]),
            Body::new(vec![Atom::new(Pred::Var(p), vec![v(0)])], Formula::top()),
        ));
        let atom = v(0)
            .tuple_proj(0)
            .equal_to(v(0).tuple_proj(1).mut_current());
        system.push_candidate_atoms(p, vec![Formula::Atom(atom)]);
        let system = flatten_recursive_pred_args(system);
        let atoms = &system.candidate_atoms[0].atoms;
        assert_eq!(atoms, &vec![Formula::Atom(v(0).equal_to(v(1)))]);
    }
}
