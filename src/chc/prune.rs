//! The clauses of a system that can constrain a solution of the predicate variables that remain.
//!
//! Two kinds of clause are left out of the emitted query, each satisfied by a constant
//! interpretation of a predicate variable that no remaining clause needs to differ from it.
//!
//! - Underivable (forward). A predicate variable is derivable when some clause whose unguarded
//!   top-level body atoms are all derivable has it in a head position: the head, or an atom under
//!   an odd number of negations or implication premises in the body. A clause with an underivable
//!   unguarded top-level body atom is left out. Interpreting every underivable variable as `false`
//!   makes the body of such a clause false, and in a remaining clause an underivable variable
//!   occurs only in body positions (a head position would make it derivable), where lowering it to
//!   `false` keeps the clause true. This removes the body of a function whose precondition no
//!   clause establishes: a function without a contract that nothing analyzed calls.
//! - Unused (backward). A predicate variable is used when it occurs in a body position of a
//!   remaining clause whose unguarded heads (the head atom and the negated top-level body atoms)
//!   are all used; a clause without such heads is a goal and always remains. A clause with an
//!   unused unguarded head is left out. Interpreting every unused variable as `true` satisfies such
//!   a clause, and in a remaining clause an unused variable occurs only in head positions, where
//!   raising it to `true` keeps the clause true. This removes the definition of a postcondition or
//!   a call result that no remaining clause reads.
//!
//! A solution of the remaining clauses, extended by those constants, is therefore a solution of
//! the whole system, and a solution of the whole system restricts to one of the remaining
//! clauses. The predicate variables applied in the bodies of user-defined predicates and in laws
//! are kept as both derivable and used, since their positions there are not followed. Dependency
//! sets are computed on the whole system before the clauses are left out, so every remaining
//! unknown is declared with the set it would have had; a constant needs no dependency.

use std::collections::HashSet;

use super::*;

/// The position of an occurrence of a predicate variable in a clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Position {
    /// A body position: a solution of the clause stays one when the variable is lowered.
    Body,
    /// A head position: a solution of the clause stays one when the variable is raised.
    Head,
}

impl Position {
    fn flip(self) -> Self {
        match self {
            Position::Body => Position::Head,
            Position::Head => Position::Body,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Occurrence {
    pred: PredVarId,
    position: Position,
    /// Whether the occurrence alone decides the clause: an unguarded top-level body atom, which
    /// makes the body false when the variable is `false`, or an unguarded head (the head atom or a
    /// negated top-level body atom), which makes the clause true when the variable is `true`.
    top_level: bool,
}

fn formula_occurrences(
    formula: &Formula,
    position: Position,
    top_level: bool,
    out: &mut Vec<Occurrence>,
) {
    match formula {
        Formula::Atom(atom) => atom_occurrences(atom, position, top_level, out),
        Formula::Not(f) => formula_occurrences(f, position.flip(), top_level, out),
        Formula::And(fs) => fs.iter().for_each(|f| {
            formula_occurrences(f, position, top_level && position == Position::Body, out)
        }),
        Formula::Or(fs) => fs.iter().for_each(|f| {
            formula_occurrences(f, position, top_level && position == Position::Head, out)
        }),
        Formula::Implies(lhs, rhs) => {
            formula_occurrences(lhs, position.flip(), false, out);
            formula_occurrences(rhs, position, false, out);
        }
        Formula::Exists(_, f) | Formula::Forall(_, f) => {
            formula_occurrences(f, position, false, out)
        }
    }
}

fn atom_occurrences(atom: &Atom, position: Position, top_level: bool, out: &mut Vec<Occurrence>) {
    if let Some(guard) = &atom.guard {
        formula_occurrences(guard, position.flip(), false, out);
    }
    if let Pred::Var(pred) = atom.pred {
        out.push(Occurrence {
            pred,
            position,
            top_level: top_level && atom.guard.is_none(),
        });
    }
}

fn clause_occurrences(clause: &Clause) -> Vec<Occurrence> {
    let mut out = Vec::new();
    atom_occurrences(&clause.head, Position::Head, true, &mut out);
    for atom in &clause.body.atoms {
        atom_occurrences(atom, Position::Body, true, &mut out);
    }
    formula_occurrences(&clause.body.formula, Position::Body, true, &mut out);
    out
}

/// The predicate variables whose positions are not followed: those applied in the formula body
/// of a user-defined predicate or in a law.
fn kept_pred_vars(system: &System) -> HashSet<PredVarId> {
    let in_laws = system
        .laws
        .values()
        .flatten()
        .flat_map(Formula::iter_atoms)
        .filter_map(|atom| match atom.pred {
            Pred::Var(id) => Some(id),
            _ => None,
        });
    system
        .pred_vars_in_definitions()
        .into_iter()
        .chain(in_laws)
        .collect()
}

/// The clauses left after removing the underivable and then the unused ones, in order.
pub fn emitted_clauses(system: &System) -> Vec<ClauseId> {
    let kept = kept_pred_vars(system);
    let occurrences: Vec<(ClauseId, Vec<Occurrence>)> = system
        .clauses
        .iter_enumerated()
        .map(|(id, clause)| (id, clause_occurrences(clause)))
        .collect();
    let derivable = derivable_clauses(&occurrences, &kept);
    used_clauses(&derivable, &kept)
        .into_iter()
        .map(|(id, _)| *id)
        .collect()
}

fn derivable_clauses<'a>(
    clauses: &'a [(ClauseId, Vec<Occurrence>)],
    kept: &HashSet<PredVarId>,
) -> Vec<&'a (ClauseId, Vec<Occurrence>)> {
    let mut derivable = kept.clone();
    let fires = |occs: &[Occurrence], derivable: &HashSet<PredVarId>| {
        occs.iter()
            .filter(|o| o.position == Position::Body && o.top_level)
            .all(|o| derivable.contains(&o.pred))
    };
    loop {
        let before = derivable.len();
        for (_, occs) in clauses {
            if fires(occs, &derivable) {
                derivable.extend(
                    occs.iter()
                        .filter(|o| o.position == Position::Head)
                        .map(|o| o.pred),
                );
            }
        }
        if derivable.len() == before {
            break;
        }
    }
    clauses
        .iter()
        .filter(|(_, occs)| fires(occs, &derivable))
        .collect()
}

fn used_clauses<'a>(
    clauses: &[&'a (ClauseId, Vec<Occurrence>)],
    kept: &HashSet<PredVarId>,
) -> Vec<&'a (ClauseId, Vec<Occurrence>)> {
    let mut used = kept.clone();
    let needed = |occs: &[Occurrence], used: &HashSet<PredVarId>| {
        occs.iter()
            .filter(|o| o.position == Position::Head && o.top_level)
            .all(|o| used.contains(&o.pred))
    };
    loop {
        let before = used.len();
        for (_, occs) in clauses {
            if needed(occs, &used) {
                used.extend(
                    occs.iter()
                        .filter(|o| o.position == Position::Body)
                        .map(|o| o.pred),
                );
            }
        }
        if used.len() == before {
            break;
        }
    }
    clauses
        .iter()
        .copied()
        .filter(|(_, occs)| needed(occs, &used))
        .collect()
}

/// The predicate variables applied in `clauses`.
pub fn pred_vars_of<'a>(clauses: impl Iterator<Item = &'a Clause>) -> HashSet<PredVarId> {
    clauses
        .flat_map(clause_occurrences)
        .map(|o| o.pred)
        .collect()
}
