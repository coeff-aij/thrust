//! The solver's refutation, read into the tree of facts it derives.
//!
//! `z3` refutes a system of clauses by hyper-resolution: each step applies one clause to facts
//! derived before, instances of the predicate variables at concrete arguments, and derives the
//! instance of its head. The last step derives the marker of the goal it refutes (see
//! [`crate::chc::System::solve_with`]), so the facts under that marker are a run of the program
//! that reaches the goal and breaks it.

use std::collections::HashMap;

use super::expr::Expr;
use super::model::{self, Sexp};

/// An instance of a predicate variable, with the facts the step deriving it applied its clause
/// to.
#[derive(Debug, Clone)]
pub struct Fact {
    /// The predicate variable's name in the query (`p3`).
    pub pred: String,
    pub args: Vec<Expr>,
    pub premises: Vec<Fact>,
}

type Env<'a> = HashMap<&'a str, &'a Sexp>;

fn resolve<'a>(mut s: &'a Sexp, env: &Env<'a>) -> &'a Sexp {
    while let Sexp::Atom(name) = s {
        match env.get(name.as_str()) {
            Some(bound) => s = bound,
            None => break,
        }
    }
    s
}

fn fact_of(s: &Sexp, env: &Env<'_>) -> Option<(String, Vec<Expr>)> {
    match resolve(s, env) {
        Sexp::Atom(name) => Some((name.clone(), Vec::new())),
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(pred), args @ ..] => {
                Some((pred.clone(), args.iter().map(model::to_expr).collect()))
            }
            _ => None,
        },
    }
}

fn is_hyper_res(head: &Sexp) -> bool {
    matches!(head, Sexp::List(h) if matches!(h.as_slice(), [Sexp::Atom(u), Sexp::Atom(r), ..] if u == "_" && r == "hyper-res"))
}

/// The facts the proof term `s` derives at its top.
fn derive<'a>(s: &'a Sexp, env: &mut Env<'a>, depth: usize) -> Vec<Fact> {
    // A refutation of a long run is deep; past this depth the rest of the run is not shown.
    if depth > 4096 {
        return Vec::new();
    }
    let items = match resolve(s, env) {
        Sexp::Atom(_) => return Vec::new(),
        Sexp::List(items) => items,
    };
    match items.as_slice() {
        [Sexp::Atom(l), Sexp::List(binds), body] if l == "let" => {
            for bind in binds {
                if let Sexp::List(pair) = bind {
                    if let [Sexp::Atom(name), value] = pair.as_slice() {
                        env.insert(name.as_str(), value);
                    }
                }
            }
            derive(body, env, depth + 1)
        }
        [head, _clause, rest @ ..] if is_hyper_res(head) => {
            let Some((conclusion, premises)) = rest.split_last() else {
                return Vec::new();
            };
            let Some((pred, args)) = fact_of(conclusion, env) else {
                return Vec::new();
            };
            let premises = premises
                .iter()
                .flat_map(|p| derive(p, env, depth + 1))
                .collect();
            vec![Fact {
                pred,
                args,
                premises,
            }]
        }
        [Sexp::Atom(a), _] if a == "asserted" => Vec::new(),
        [_, args @ ..] => args
            .iter()
            .flat_map(|a| derive(a, env, depth + 1))
            .collect(),
        [] => Vec::new(),
    }
}

/// The facts a refutation as `z3` prints it after `(get-proof)` derives last.
pub fn read(proof: &str) -> Vec<Fact> {
    let tokens = model::tokens(proof);
    let mut pos = 0;
    let Some(Sexp::List(items)) = model::parse(&tokens, &mut pos) else {
        return Vec::new();
    };
    let Some(term) = items.iter().find_map(|item| match item {
        Sexp::List(parts) => match parts.as_slice() {
            [Sexp::Atom(p), term] if p == "proof" => Some(term),
            _ => None,
        },
        _ => None,
    }) else {
        return Vec::new();
    };
    let mut env = Env::new();
    derive(term, &mut env, 0)
}

/// The first fact of `pred` in the tree under `facts`.
pub fn find<'a>(facts: &'a [Fact], pred: &str) -> Option<&'a Fact> {
    facts.iter().find_map(|f| {
        if f.pred == pred {
            return Some(f);
        }
        find(&f.premises, pred)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_hyper_resolution_steps() {
        let proof = "((set-logic HORN)\n(declare-fun query!0 (Int) Bool)\n(proof\n(let (($x1 (query!0 6)))\n(let ((@x2 (asserted (forall ((A Int) (B Int)) (=> (and (P B) (= A (+ 1 B))) (P A))))))\n(let ((@x3 ((_ hyper-res 0 0 0 1) @x2 ((_ hyper-res 0 0) (asserted (P 0)) (P 0)) (P 1))))\n(mp ((_ hyper-res 0 0 0 1) (asserted (forall ((A Int)) (=> (P A) (query!0 A)))) @x3 $x1) (asserted (=> $x1 false)) false))))))";
        let facts = read(proof);
        assert_eq!(facts.len(), 1);
        assert_eq!(facts[0].pred, "query!0");
        assert_eq!(facts[0].args, vec![Expr::sym("6")]);
        let p1 = find(&facts, "P").unwrap();
        assert_eq!(p1.args, vec![Expr::sym("1")]);
        assert_eq!(p1.premises[0].args, vec![Expr::sym("0")]);
    }
}
