//! The goal the solver refuted and the run of the program its refutation gives: each fact with
//! the constraint that derives it from the facts below it.

use std::collections::HashMap;

use rustc_span::def_id::LocalDefId;

use crate::chc;

use super::formula::{OneLine, Term};
use super::proof::{self, Fact};
use super::sites::{Names, Owner, PredInfo};

/// At most this many facts of the run are shown.
const MAX_STEPS: usize = 80;

/// A run of a loop longer than this is shown by its first and last states.
const MAX_CHAIN: usize = 3;

#[derive(Debug, Clone)]
pub struct Step {
    pub depth: usize,
    pub fact: String,
    /// The fact's unknown and the values of the arguments the program names (the latest state
    /// of a loop shown by its first and last).
    pub pred: String,
    pub args: Vec<(String, String)>,
    /// The constraint deriving the fact, when one clause of the system matches the step.
    pub via: Option<chc::ClauseId>,
}

#[derive(Debug, Clone)]
pub struct Failure {
    pub goal: chc::ClauseId,
    pub run: Vec<Step>,
    pub truncated: bool,
    /// The values the goal's variables have where it fails, by their index.
    pub values: Vec<Term>,
    /// The functions whose inferred contract the run goes through: a wrong result of theirs
    /// shows here.
    pub inferred: Vec<LocalDefId>,
    /// Whether the run is `z3`'s, asked of a query the solver refuted without one.
    pub by_z3: bool,
}

impl Failure {
    /// The values where the goal fails of the variables of `goal` the program names, and of those
    /// it does not name that its formula still reads, once each.
    pub fn named_values(&self, goal: &super::constraints::Constraint) -> Vec<(String, String)> {
        let mut shown: Vec<(String, String)> = Vec::new();
        for (name, value) in goal.vars.iter().zip(&self.values) {
            // A variable the program does not name is shown where the constraint still reads it.
            if name.starts_with("__tmp_chc_") && !goal.formula.contains(name.as_str()) {
                continue;
            }
            for (name, value) in named(name, value) {
                // A unit value tells nothing.
                if value != "()" && shown.iter().all(|(n, _)| *n != name) {
                    shown.push((name, value));
                }
            }
        }
        shown
    }
}

/// `name = value`, a `&mut` pair `<c, f>` as its current value `*name = c` and its final one
/// `°name = f` (see [`super::formula::components`]).
fn named(name: &str, value: &Term) -> Vec<(String, String)> {
    super::formula::components(name, value.clone())
        .into_iter()
        .map(|(name, value)| (name, value.one_line()))
        .collect()
}

struct Reader<'a> {
    /// The clause each tag marks, by its name in the query (see `chc::System::solve_with`).
    tags: HashMap<String, chc::ClauseId>,
    /// The facts shown so far.
    shown: std::collections::HashSet<String>,
    names: &'a Names,
    /// The report's view of each predicate variable, by its name in the query.
    preds: HashMap<String, (chc::PredVarId, &'a PredInfo)>,
    run: Vec<Step>,
    truncated: bool,
    /// The functions whose inferred contract the run goes through, by their `post`.
    inferred: Vec<LocalDefId>,
}

impl Reader<'_> {
    /// The arguments of `fact` the program names, each with what it stands for, and `…` for those
    /// it does not.
    fn args(&self, fact: &Fact) -> String {
        let (named, unnamed) = self.named_args(fact);
        let mut shown: Vec<String> = named.iter().map(|(n, v)| format!("{n} = {v}")).collect();
        if unnamed {
            shown.push("…".to_owned());
        }
        shown.join(", ")
    }

    /// The arguments of `fact` the program names, each once, and whether it has others.
    fn named_args(&self, fact: &Fact) -> (Vec<(String, String)>, bool) {
        let (values, names) = match self.preds.get(&fact.pred) {
            Some((p, info)) => (self.names.arrange(*p, &fact.args), info.args.as_slice()),
            None => (fact.args.clone(), [].as_slice()),
        };
        let mut shown: Vec<(String, String)> = Vec::new();
        let mut unnamed = false;
        for (k, value) in values.iter().enumerate() {
            let Some(name) = names.get(k).cloned().flatten() else {
                unnamed = true;
                continue;
            };
            for arg in named(&name, value) {
                if !shown.contains(&arg) {
                    shown.push(arg);
                }
            }
        }
        (shown, unnamed)
    }

    fn name(&self, fact: &Fact) -> String {
        self.preds
            .get(&fact.pred)
            .map(|(_, info)| info.name.clone())
            .unwrap_or_else(|| fact.pred.clone())
    }

    /// The clause the step deriving `fact` applies: the one whose tag is among its premises.
    fn via(&self, fact: &Fact) -> Option<chc::ClauseId> {
        fact.premises
            .iter()
            .find_map(|p| self.tags.get(&p.pred).copied())
    }

    /// Whether `fact` is not shown in the run: a clause's tag, or an unknown every solution
    /// makes true (a function's entry being reached).
    fn is_tag(&self, fact: &Fact) -> bool {
        let always_true = self
            .preds
            .get(&fact.pred)
            .is_some_and(|(p, _)| self.names.always_true.contains(p));
        self.tags.contains_key(&fact.pred) || always_true
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
        // A fact the run reaches by two ways is shown once.
        let key = format!("{}({})", self.name(fact), self.args(fact));
        if !self.shown.insert(key) {
            return;
        }
        if let Some((_, info)) = self.preds.get(&fact.pred) {
            if let Owner::Contract { def, ret: true } = info.owner {
                if !self.inferred.contains(&def) {
                    self.inferred.push(def);
                }
            }
        }
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
            pred: self.name(fact),
            args: self.named_args(fact).0,
            via: self.via(fact),
        };
        if !self.push(step) {
            return;
        }
        let below = if chain.len() > MAX_CHAIN { last } else { fact };
        for premise in &below.premises {
            if self.is_tag(premise) {
                continue;
            }
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
pub fn read(
    answer: &chc::Answer,
    names: &Names,
    symbols: &crate::chc::answer::Symbols,
) -> Option<Failure> {
    let facts = proof::read(answer.proof.as_ref()?, symbols);
    let (marker, goal) = answer
        .goal_markers
        .iter()
        .find_map(|(marker, goal)| Some((proof::find(&facts, &marker.to_string())?, *goal)))?;
    let preds = names
        .preds
        .iter()
        .map(|(p, info)| (p.to_string(), (*p, info)))
        .collect();
    let tags = answer
        .clause_tags
        .iter()
        .map(|(tag, clause)| (tag.to_string(), *clause))
        .collect();
    let mut reader = Reader {
        tags,
        shown: std::collections::HashSet::new(),
        names,
        preds,
        run: Vec::new(),
        truncated: false,
        inferred: Vec::new(),
    };
    // Shown from the run's end: the premises of the goal, the facts below them, and so on.
    for premise in &marker.premises {
        if !reader.is_tag(premise) {
            reader.walk(premise, 0);
        }
    }
    Some(Failure {
        goal,
        run: reader.run,
        truncated: reader.truncated,
        values: marker.args.clone(),
        inferred: reader.inferred,
        by_z3: answer.proof_by_z3,
    })
}
