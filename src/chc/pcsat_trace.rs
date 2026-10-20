//! The goals PCSat refutes, read from its refutation and its debug log, for a query where `z3`
//! gives no refutation.
//!
//! PCSat prints no refutation over the clauses it is given: its preprocessing rewrites them,
//! and its evidence of `unsat` is over the rewritten clauses. So every goal is marked by one
//! unknown `g` over the goal's number ([`super::System::mark_goals_by_number`]), and a number
//! PCSat reaches `g` at is read off what it prints:
//!
//! - when it refutes by learning from examples, the atoms of `g` in the conflict its refutation
//!   (`print_unsat_witness`, on stdout) ends in;
//! - when its preprocessing refutes the clauses, the lower bound it gives `g` in its debug log
//!   (a `dbg_` configuration, on stderr), `not (1 != x)` for the goal `1`.
//!
//! A query with one goal names it without either. When what PCSat prints names several goals or
//! none, the system is solved once more with one goal at a time ([`super::System`]'s
//! `refuted_alone`). The debug log also gives the lower bounds of the other unknowns: what
//! reaches them.
//!
//! What PCSat prints is text for a person, which fptprove does not keep stable: this reads the
//! lines the develop builds of 2026-10 print, and passes over a line it does not know.

use std::collections::HashMap;

/// A bound PCSat gives an unknown: its parameters, as the log names them, and the formula over
/// them, as it prints it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bound {
    pub params: Vec<String>,
    pub formula: String,
}

/// What PCSat prints, by the names of the query.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Trace {
    /// The numbers of the goals PCSat reaches the marker at: the goal it refutes when there is
    /// one, one of them when there are several.
    pub goals: Vec<usize>,
    /// The last lower bound of each unknown the log gives one.
    pub lower_bounds: HashMap<String, Bound>,
}

/// Reads `refutation` (stdout) and `log` (stderr) of PCSat refuting a query whose `count` goals
/// are marked by the unknown `marker`.
pub fn read(refutation: &str, log: &str, marker: &str, count: usize) -> Trace {
    let mut trace = Trace::default();
    for line in log.lines() {
        if let Some((pred, bound)) = lower_bound(line) {
            trace.lower_bounds.insert(pred.to_owned(), bound);
        }
    }
    let in_conflicts = refutation
        .lines()
        .filter(|line| line.contains("(unsat-witness (") && line.contains("conflict "))
        .flat_map(|line| numbers_applied(line, marker));
    push_all(&mut trace.goals, in_conflicts, count);
    if trace.goals.is_empty() {
        let bounded = log
            .lines()
            .filter_map(lower_bound)
            .filter(|(pred, _)| *pred == marker)
            .flat_map(|(_, bound)| numbers_bounded(&bound));
        push_all(&mut trace.goals, bounded, count);
    }
    if count == 1 {
        trace.goals = vec![0];
    }
    trace
}

/// What PCSat prints, by the goals and unknowns of the system.
#[derive(Debug, Clone)]
pub struct Refutation {
    /// The goals PCSat reaches the marker at: the goal it refutes, or one of them.
    pub goals: Vec<super::ClauseId>,
    pub lower_bounds: Vec<LowerBound>,
}

/// PCSat's lower bound of an unknown of the system.
#[derive(Debug, Clone)]
pub struct LowerBound {
    pub pred: super::PredVarId,
    /// The forall predicates the unknown depends on (`declare-dep-exists-fun`), which PCSat
    /// takes as its first parameters, before the unknown's own arguments.
    pub dependencies: Vec<String>,
    pub bound: Bound,
}

impl Refutation {
    /// `trace` with each goal number as the goal `goals` numbers, and each unknown as `preds`
    /// names it, with the forall predicates `dependencies` gives it; the bounds of other
    /// unknowns (the marker's, those PCSat makes) are left out.
    pub fn of(
        trace: Trace,
        goals: &[super::ClauseId],
        preds: &HashMap<String, super::PredVarId>,
        dependencies: &HashMap<super::PredVarId, std::collections::BTreeSet<super::ForallPred>>,
    ) -> Self {
        let mut lower_bounds: Vec<LowerBound> = trace
            .lower_bounds
            .into_iter()
            .filter_map(|(name, bound)| {
                let pred = *preds.get(&name)?;
                let dependencies = dependencies
                    .get(&pred)
                    .map(|deps| deps.iter().map(ToString::to_string).collect())
                    .unwrap_or_default();
                Some(LowerBound {
                    pred,
                    dependencies,
                    bound,
                })
            })
            .collect();
        lower_bounds.sort_by_key(|b| b.pred.index());
        Refutation {
            goals: trace.goals.iter().map(|i| goals[*i]).collect(),
            lower_bounds,
        }
    }
}

/// `LB of p((#tvar1:int) (#tvar2:int)): φ` as `p` and its bound.
fn lower_bound(line: &str) -> Option<(&str, Bound)> {
    let rest = line.strip_prefix("LB of ")?;
    let (pred, rest) = rest.split_once('(')?;
    let (params, formula) = rest.split_once("): ")?;
    let params = params
        .split('(')
        .filter_map(|p| Some(p.split_once(':')?.0.trim().to_owned()))
        .collect();
    let bound = Bound {
        params,
        formula: formula.to_owned(),
    };
    Some((pred, bound))
}

/// The numbers `marker` is applied to in `line`, as PCSat prints an atom, `g(1)`, or with the
/// forall predicates it depends on before the number, `g(f, 1)`.
fn numbers_applied(line: &str, marker: &str) -> Vec<usize> {
    let open = format!("{marker}(");
    let mut numbers = Vec::new();
    let mut rest = line;
    while let Some(at) = rest.find(&open) {
        // A longer name ending in the marker's (`p10` in `p110(`) is another unknown.
        let follows_name = rest[..at]
            .chars()
            .last()
            .is_some_and(|c| c.is_alphanumeric() || c == '_');
        let args = &rest[at + open.len()..];
        let Some(end) = closing(args) else {
            break;
        };
        let last = args[..end].rsplit(',').next().unwrap_or_default().trim();
        if let (false, Ok(n)) = (follows_name, last.parse()) {
            numbers.push(n);
        }
        rest = &args[end..];
    }
    numbers
}

/// The position of the parenthesis closing the one `text` follows.
fn closing(text: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' if depth == 0 => return Some(i),
            ')' => depth -= 1,
            _ => {}
        }
    }
    None
}

/// The numbers `bound` compares its last parameter, the goal's number, with: `x = 1`,
/// `x != 1`, `1 = x` or `1 != x`.
fn numbers_bounded(bound: &Bound) -> Vec<usize> {
    let Some(param) = bound.params.last() else {
        return Vec::new();
    };
    let words: Vec<&str> = bound
        .formula
        .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
        .filter(|w| !w.is_empty())
        .collect();
    let mut numbers = Vec::new();
    for window in words.windows(3) {
        let [left, op, right] = window else {
            continue;
        };
        if !matches!(*op, "=" | "!=") {
            continue;
        }
        let number: Option<usize> = match (*left == param, *right == param) {
            (true, false) => right.parse().ok(),
            (false, true) => left.parse().ok(),
            _ => None,
        };
        numbers.extend(number);
    }
    numbers
}

/// Adds each of `numbers` below `count` to `goals` once.
fn push_all(goals: &mut Vec<usize>, numbers: impl Iterator<Item = usize>, count: usize) {
    for n in numbers {
        if n < count && !goals.contains(&n) {
            goals.push(n);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_conflict_on_the_marker_names_the_goal() {
        let refutation = "\
unsat
(unsat-witness (propagation-conflict p10(1) p2(mut<Seq<Int>> (seq.empty) (seq.empty), 3))
 (positives
  (example ( => p10(0))))";
        let trace = read(refutation, "", "p10", 2);
        assert_eq!(trace.goals, [1]);
    }

    #[test]
    fn the_number_is_the_last_argument_after_dependencies() {
        let refutation =
            "(unsat-witness (propagation-conflict p23(const (const (<false>)), 5) p230(4))";
        let trace = read(refutation, "", "p23", 7);
        assert_eq!(trace.goals, [5]);
    }

    #[test]
    fn the_lower_bound_of_the_marker_names_the_goals_without_a_conflict() {
        let log = "\
LB of p5((#tvar30:int)): not (1 != #tvar30)
LB of p2((#tvar31:int) (#tvar32:int)): not (#tvar31 != #tvar32)
LB of p6((#tvar1:a0 ->> int) (#tvar2:int)): exists (#tvar3:a0). not (#tvar2 != 0 \\/ #tvar1[#tvar3] = 1)";
        let refuted = "unsat\n(unsat-witness (false-constraint)\n false)";
        let trace = read(refuted, log, "p5", 3);
        assert_eq!(trace.goals, [1]);
        let bound = &trace.lower_bounds["p2"];
        assert_eq!(bound.params, ["#tvar31", "#tvar32"]);
        assert_eq!(bound.formula, "not (#tvar31 != #tvar32)");
        assert_eq!(read(refuted, log, "p6", 3).goals, [0]);
    }
}
