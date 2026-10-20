//! What PCSat's debug log says about a query it refutes, for a refutation where `z3` gives none.
//!
//! PCSat prints no refutation over the query it is given: its preprocessing eliminates the
//! unknowns one by one, by their bounds or by resolution, and a query it refutes there ends in a
//! clause `false` its evidence does not trace back to the query's clauses. Its debug log (a
//! `dbg_` configuration, on stderr) names the unknowns it eliminates, so each goal is given a
//! marker of its own ([`super::System::mark_goals_by_name`]) and the log is read for the
//! markers: a goal whose marker is resolved in the round that derives `false` is refuted, one
//! whose marker has no lower bound or no clause left defining it holds. The lower bound of an
//! unknown is what reaches it: the facts the refutation goes through.
//!
//! The log is text for a person, which fptprove does not keep stable: this reads the lines the
//! develop builds of 2026-10 print, and a line it does not know is passed over.

use std::collections::HashMap;

/// Why the log shows a goal holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Held {
    /// Its marker has no lower bound: no clause reaches the goal.
    NoLowerBound,
    /// No clause defining its marker is left: the eliminations before it removed them.
    NotReached,
}

impl std::fmt::Display for Held {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Held::NoLowerBound => f.write_str("nothing reaches it"),
            Held::NotReached => f.write_str("no clause reaching it is left"),
        }
    }
}

/// A bound PCSat gives an unknown: its parameters, as the log names them, and the formula over
/// them, as it prints it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bound {
    pub params: Vec<String>,
    pub formula: String,
}

/// What the log says, by the names of the query.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Trace {
    /// The markers of the goals refuted: each resolved alone in a round that derives `false`.
    pub refuted: Vec<String>,
    /// The markers of the goals one of which is refuted: resolved together in a round that
    /// derives `false`, or left to the unfolding PCSat refutes the rest by.
    pub candidates: Vec<String>,
    /// The markers of the goals the log shows hold.
    pub held: Vec<(String, Held)>,
    /// The last lower bound of each unknown the log gives one.
    pub lower_bounds: HashMap<String, Bound>,
}

/// What the log says, by the goals and unknowns of the system.
#[derive(Debug, Clone)]
pub struct Refutation {
    pub refuted: Vec<super::ClauseId>,
    pub candidates: Vec<super::ClauseId>,
    pub held: Vec<(super::ClauseId, Held)>,
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
    /// `trace` with each marker as the goal `goals` gives it, and each unknown as `preds` does,
    /// with the forall predicates `dependencies` gives it; the bounds of other unknowns (the
    /// markers', those PCSat makes) are left out.
    pub fn of(
        trace: Trace,
        goals: &HashMap<String, super::ClauseId>,
        preds: &HashMap<String, super::PredVarId>,
        dependencies: &HashMap<super::PredVarId, std::collections::BTreeSet<super::ForallPred>>,
    ) -> Self {
        let goal = |marker: &String| goals[marker];
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
            refuted: trace.refuted.iter().map(goal).collect(),
            candidates: trace.candidates.iter().map(goal).collect(),
            held: trace.held.iter().map(|(m, why)| (goal(m), *why)).collect(),
            lower_bounds,
        }
    }
}

/// Reads `log`, the debug log of PCSat refuting a query whose goals are marked by the unknowns
/// `is_marker` tells.
pub fn read(log: &str, is_marker: impl Fn(&str) -> bool) -> Trace {
    let mut trace = Trace::default();
    let mut eliminated: Vec<&str> = Vec::new();
    let mut this_round: Vec<&str> = Vec::new();
    let mut unfolded = false;
    let lines: Vec<&str> = log.lines().collect();
    for (i, line) in lines.iter().enumerate() {
        if let Some(marker) = held(line).filter(|(m, _)| is_marker(m)) {
            trace.held.push((marker.0.to_owned(), marker.1));
        } else if line.starts_with("[elim_pvs] begin elim_pvars_by_resolution") {
            this_round.clear();
        } else if let Some(pred) = line.strip_prefix("eliminating ") {
            this_round.push(pred.trim());
            eliminated.push(pred.trim());
        } else if let Some((pred, bound)) = lower_bound(line) {
            trace.lower_bounds.insert(pred.to_owned(), bound);
        } else if line.starts_with("[elim_pvs] begin result") && derives_false(&lines[i + 1..]) {
            let markers = unsettled(&this_round, &trace, &is_marker);
            match markers.as_slice() {
                [one] => push_new(&mut trace.refuted, one),
                _ => markers
                    .iter()
                    .for_each(|m| push_new(&mut trace.candidates, m)),
            }
        } else if line.starts_with("[unfold-refute] depth") && line.contains(" refuted in ") {
            unfolded = true;
        }
    }
    if unfolded || (trace.refuted.is_empty() && trace.candidates.is_empty()) {
        for m in unsettled(&eliminated, &trace, &is_marker) {
            push_new(&mut trace.candidates, &m);
        }
    }
    trace.candidates.retain(|m| !trace.refuted.contains(m));
    if trace.refuted.is_empty() && trace.candidates.len() == 1 {
        trace.refuted = std::mem::take(&mut trace.candidates);
    }
    trace
}

/// The marker a line shows holds, and why.
fn held(line: &str) -> Option<(&str, Held)> {
    if let Some(pred) = line.strip_suffix(" is assigned false because there is no LB") {
        return Some((pred, Held::NoLowerBound));
    }
    let rest = line.strip_prefix("[safe] ")?;
    let (pred, rest) = rest.split_once(' ')?;
    rest.contains("occurs 0 times positively")
        .then_some((pred, Held::NotReached))
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

/// Whether the clauses a `begin result` line lists (indented below it) include `false`.
fn derives_false(below: &[&str]) -> bool {
    below
        .iter()
        .take_while(|l| l.starts_with("  "))
        .any(|l| l.trim() == "false")
}

/// The markers among `preds` the log has not settled yet.
fn unsettled(preds: &[&str], trace: &Trace, is_marker: impl Fn(&str) -> bool) -> Vec<String> {
    preds
        .iter()
        .filter(|p| is_marker(p))
        .filter(|p| trace.held.iter().all(|(h, _)| h != *p))
        .map(|p| (*p).to_owned())
        .collect()
}

fn push_new(list: &mut Vec<String>, item: &str) {
    if !list.iter().any(|i| i == item) {
        list.push(item.to_owned());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn marker(name: &str) -> bool {
        name.starts_with('g')
    }

    #[test]
    fn a_goal_resolved_alone_into_false_is_refuted() {
        let log = "\
g1 is assigned false because there is no LB
LB of p2((#tvar30:int) (#tvar31:int)): not (#tvar30 != #tvar31)
[elim_pvs] begin elim_pvars_by_resolution [3]:
eliminating p2
eliminating g0
[elim_pvs] begin result [1]:
  false
";
        let trace = read(log, marker);
        assert_eq!(trace.refuted, ["g0"]);
        assert!(trace.candidates.is_empty());
        assert_eq!(trace.held, [("g1".to_owned(), Held::NoLowerBound)]);
        let bound = &trace.lower_bounds["p2"];
        assert_eq!(bound.params, ["#tvar30", "#tvar31"]);
        assert_eq!(bound.formula, "not (#tvar30 != #tvar31)");
    }

    #[test]
    fn goals_resolved_together_into_false_are_candidates() {
        let log = "\
[elim_pvs] begin elim_pvars_by_resolution [5]:
[safe] g6 (arity 1) occurs 0 times positively and 1 times negatively (at 0.03 s)
eliminating g6
eliminating g2
eliminating g4
[elim_pvs] begin result [1]:
  false
";
        let trace = read(log, marker);
        assert!(trace.refuted.is_empty());
        assert_eq!(trace.candidates, ["g2", "g4"]);
        assert_eq!(trace.held, [("g6".to_owned(), Held::NotReached)]);
    }

    #[test]
    fn the_goal_left_to_unfolding_is_refuted() {
        let log = "\
[elim_pvs] begin elim_pvars_by_resolution [4]:
eliminating g3
eliminating p4
[elim_pvs] begin result [3]:
  p2 1 1
[unfold-refute] depth 12: 1 goal resolvent(s): resolvent 0 refuted in 0.01 s
";
        let trace = read(log, marker);
        assert_eq!(trace.refuted, ["g3"]);
    }
}
