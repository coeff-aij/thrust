//! The solver's interpretations simplified by `z3` into equivalent formulas: its quantifier
//! elimination, then simplification, then simplification of each part under the others, repeated
//! until nothing changes (`(then qe simplify (repeat (then ctx-solver-simplify simplify) 10))`;
//! one pass leaves contradictory disjuncts the next removes). Each tactic keeps the formula's
//! meaning, and an
//! interpretation `z3` cannot take back (one applying a function of the query) or does not
//! simplify in time is shown as it was.

use std::collections::HashMap;

use super::model::{self, Interpretation};

const TACTIC: &str = "(then qe simplify (repeat (then ctx-solver-simplify simplify) 10))";

/// How long `z3` may spend on one interpretation, in milliseconds.
const BUDGET_MS: u32 = 5000;

/// The declarations of `query`: everything but its comments, assertions and commands.
fn declarations(query: &str) -> String {
    query
        .lines()
        .filter(|line| {
            let line = line.trim_start();
            !(line.starts_with(';')
                || line.starts_with("(assert")
                || line.starts_with("(check-sat")
                || line.starts_with("(set-logic")
                || line.starts_with("(set-info"))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Replaces the body of each of `interpretations` by `z3`'s simplification of it, over the
/// declarations of `query`, `run` giving a script to `z3` and returning what it prints.
pub fn simplify(
    interpretations: &mut HashMap<String, Interpretation>,
    query: &str,
    symbols: &model::Symbols,
    run: impl Fn(&str) -> Option<String>,
) {
    let mut names: Vec<&String> = interpretations.keys().collect();
    names.sort();
    let mut script = declarations(query);
    script.push('\n');
    let prelude_len = script.len();
    for name in &names {
        let Some((params, body)) = &interpretations[*name].source else {
            continue;
        };
        script.push_str(&format!("(echo \"@{name}\")\n(push)\n"));
        for (param, sort) in params {
            script.push_str(&format!("(declare-const {param} {sort})\n"));
        }
        script.push_str(&format!(
            "(assert {body})\n(apply (try-for {TACTIC} {BUDGET_MS}))\n(pop)\n"
        ));
    }
    if script.len() == prelude_len {
        return;
    }
    let Some(output) = run(&script) else {
        return;
    };
    for section in output.split("@").skip(1) {
        let Some((name, text)) = section.split_once('\n') else {
            continue;
        };
        let (Some(simplified), Some(interpretation)) = (
            model::read_goals(text, symbols),
            interpretations.get_mut(name.trim()),
        ) else {
            continue;
        };
        interpretation.body = simplified;
    }
}
