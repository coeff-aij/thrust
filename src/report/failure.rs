//! The goal the solver refuted and the run of the program its refutation gives: each fact with
//! the constraint that derives it from the facts below it.

use std::collections::HashMap;

use crate::chc;

use super::proof::{self, Fact};
use super::sites::{Names, PredInfo};

/// At most this many facts of the run are shown.
const MAX_STEPS: usize = 80;

/// A run of a loop longer than this is shown by its first and last states.
const MAX_CHAIN: usize = 3;

#[derive(Debug, Clone)]
pub struct Step {
    pub depth: usize,
    pub fact: String,
    /// The constraint deriving the fact, when one clause of the system matches the step.
    pub via: Option<chc::ClauseId>,
}

#[derive(Debug, Clone)]
pub struct Failure {
    pub goal: chc::ClauseId,
    pub run: Vec<Step>,
    pub truncated: bool,
}

struct Reader<'a> {
    system: &'a chc::System,
    names: &'a Names,
    /// The report's view of each predicate variable, by its name in the query.
    preds: HashMap<String, (chc::PredVarId, &'a PredInfo)>,
    run: Vec<Step>,
    truncated: bool,
}

impl Reader<'_> {
    /// The arguments of `fact`, each with what it stands for, the results apart from the rest.
    fn args(&self, fact: &Fact) -> String {
        let info = self.preds.get(&fact.pred).map(|(_, info)| *info);
        let names = info.map(|info| &info.args);
        let results = info.map_or(0, |info| info.results);
        let values = match info {
            Some(_) => self
                .names
                .pred_head(self.preds[&fact.pred].0)
                .arrange(&fact.args),
            None => fact.args.clone(),
        };
        let mut out = String::new();
        for (k, value) in values.iter().enumerate() {
            let sep = match k {
                0 => "",
                k if k == results => "; ",
                _ => ", ",
            };
            out.push_str(sep);
            match names.and_then(|n| n.get(k)).cloned().flatten() {
                Some(name) => out.push_str(&format!("{name} = {value}")),
                None => out.push_str(&value.to_string()),
            }
        }
        out
    }

    fn name(&self, fact: &Fact) -> String {
        self.preds
            .get(&fact.pred)
            .map(|(_, info)| info.name.clone())
            .unwrap_or_else(|| fact.pred.clone())
    }

    /// The clause the step deriving `fact` applies: the one clause whose head is the fact's
    /// predicate variable and whose body has the premises' ones, and others the solver may have
    /// resolved away beforehand.
    fn via(&self, fact: &Fact) -> Option<chc::ClauseId> {
        let pred = self.preds.get(&fact.pred)?.0;
        let premises: Vec<&str> = fact.premises.iter().map(|p| p.pred.as_str()).collect();
        let mut matching = self.system.clauses.iter_enumerated().filter(|(_, clause)| {
            if clause.head.pred != chc::Pred::Var(pred) {
                return false;
            }
            let mut body: Vec<String> = clause
                .body
                .atoms
                .iter()
                .filter_map(|a| match a.pred {
                    chc::Pred::Var(p) => Some(p.to_string()),
                    _ => None,
                })
                .collect();
            premises
                .iter()
                .all(|p| match body.iter().position(|b| b == p) {
                    Some(i) => {
                        body.swap_remove(i);
                        true
                    }
                    None => false,
                })
        });
        let (id, _) = matching.next()?;
        matching.next().is_none().then_some(id)
    }

    fn push(&mut self, step: Step) -> bool {
        if self.run.len() >= MAX_STEPS {
            self.truncated = true;
            return false;
        }
        self.run.push(step);
        true
    }

    fn walk(&mut self, fact: &Fact, depth: usize) {
        let mut chain = vec![fact];
        while let Some(next) = single_same(chain.last().unwrap()) {
            chain.push(next);
        }
        let last = *chain.last().unwrap();
        let text = if chain.len() > MAX_CHAIN {
            let states: Vec<String> = chain
                .iter()
                .rev()
                .map(|f| format!("({})", self.args(f)))
                .collect();
            let shown = [&states[..2], &["…".to_owned()], &states[states.len() - 1..]].concat();
            format!(
                "{} × {}: {}",
                self.name(fact),
                chain.len(),
                shown.join(" → ")
            )
        } else {
            format!("{}({})", self.name(fact), self.args(fact))
        };
        let step = Step {
            depth,
            fact: text,
            via: self.via(fact),
        };
        if !self.push(step) {
            return;
        }
        let below = if chain.len() > MAX_CHAIN { last } else { fact };
        for premise in &below.premises {
            if chain.len() <= MAX_CHAIN || premise.pred != fact.pred {
                self.walk(premise, depth + 1);
            }
        }
    }
}

/// The one premise of `fact` of its own predicate variable: the previous state of a loop.
fn single_same(fact: &Fact) -> Option<&Fact> {
    let mut same = fact.premises.iter().filter(|p| p.pred == fact.pred);
    let next = same.next()?;
    same.next().is_none().then_some(next)
}

/// The refuted goal and its run, if the answer is a refutation that derives a goal's marker.
pub fn read(answer: &chc::Answer, system: &chc::System, names: &Names) -> Option<Failure> {
    let facts = proof::read(answer.proof.as_ref()?);
    let (marker, goal) = answer
        .goal_markers
        .iter()
        .find_map(|(marker, goal)| Some((proof::find(&facts, &marker.to_string())?, *goal)))?;
    let preds = names
        .preds
        .iter()
        .map(|(p, info)| (p.to_string(), (*p, info)))
        .collect();
    let mut reader = Reader {
        system,
        names,
        preds,
        run: Vec::new(),
        truncated: false,
    };
    // Shown from the run's end: the premises of the goal, the facts below them, and so on.
    for premise in &marker.premises {
        reader.walk(premise, 0);
    }
    Some(Failure {
        goal,
        run: reader.run,
        truncated: reader.truncated,
    })
}
