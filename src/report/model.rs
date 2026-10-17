//! The solver's model, read into [`Expr`]s: the interpretation of each predicate variable.

use std::collections::HashMap;

use super::expr::Expr;
use crate::chc::format_context::DeclaredSymbol;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

pub(super) fn tokens(text: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            '(' | ')' => {
                tokens.push(c.to_string());
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '|' => {
                chars.next();
                let quoted: String = chars.by_ref().take_while(|&c| c != '|').collect();
                tokens.push(quoted);
            }
            '"' => {
                chars.next();
                let quoted: String = chars.by_ref().take_while(|&c| c != '"').collect();
                tokens.push(format!("\"{quoted}\""));
            }
            _ => {
                let mut atom = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                tokens.push(atom);
            }
        }
    }
    tokens
}

pub(super) fn parse(tokens: &[String], pos: &mut usize) -> Option<Sexp> {
    let token = tokens.get(*pos)?;
    *pos += 1;
    match token.as_str() {
        "(" => {
            let mut items = Vec::new();
            loop {
                if tokens.get(*pos)? == ")" {
                    *pos += 1;
                    return Some(Sexp::List(items));
                }
                items.push(parse(tokens, pos)?);
            }
        }
        ")" => None,
        atom => Some(Sexp::Atom(atom.to_owned())),
    }
}

fn bindings(s: &Sexp) -> Vec<(String, &Sexp)> {
    let Sexp::List(items) = s else {
        return Vec::new();
    };
    items
        .iter()
        .filter_map(|b| match b {
            Sexp::List(pair) if pair.len() == 2 => match &pair[0] {
                Sexp::Atom(name) => Some((name.clone(), &pair[1])),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

fn z3_bound_name(name: &str) -> String {
    let name: String = name.chars().filter(|c| c.is_alphanumeric()).collect();
    format!("__tmp_z3_model_{name}")
}

/// What the symbols the query declares for datatypes stand for, as the query says (see
/// `chc::System::declared_symbols`), to read the solver's answers over them.
#[derive(Debug, Default)]
pub struct Symbols(HashMap<String, DeclaredSymbol>);

impl Symbols {
    pub fn new(declared: Vec<(String, DeclaredSymbol)>) -> Self {
        Symbols(declared.into_iter().collect())
    }

    /// A sort of the solver's answer as [`super::expr::sort_name`] writes Thrust's: a datatype by
    /// the sort it stands for, `(_ BitVec 32)` as `BitVec<32>`, `(Seq Int)` as `Seq<Int>`.
    fn sort(&self, s: &Sexp) -> String {
        match s {
            Sexp::Atom(a) => match self.0.get(a) {
                Some(DeclaredSymbol::Sort(sort)) => super::expr::sort_name(sort),
                _ => a.clone(),
            },
            Sexp::List(items) => match items.as_slice() {
                [Sexp::Atom(u), Sexp::Atom(bv), Sexp::Atom(w)] if u == "_" && bv == "BitVec" => {
                    format!("BitVec<{w}>")
                }
                [Sexp::Atom(head), args @ ..] => {
                    let args: Vec<String> = args.iter().map(|a| self.sort(a)).collect();
                    format!("{head}<{}>", args.join(", "))
                }
                _ => items
                    .iter()
                    .map(|i| self.sort(i))
                    .collect::<Vec<_>>()
                    .join(" "),
            },
        }
    }

    /// `head` applied to `args`, a constructor or selector of a `Box`, a `Mut` or a tuple read as
    /// the annotations write it.
    fn applied(&self, head: &str, args: Vec<Expr>) -> Expr {
        match self.0.get(head) {
            Some(DeclaredSymbol::BoxCtor) if args.len() == 1 => args.into_iter().next().unwrap(),
            Some(DeclaredSymbol::MutCtor) => Expr::app("Mut::new", args),
            Some(DeclaredSymbol::TupleCtor) => Expr::app("tuple", args),
            Some(DeclaredSymbol::Current) => Expr::app("deref", args),
            Some(DeclaredSymbol::Final) => Expr::app("final", args),
            Some(DeclaredSymbol::Field(i)) => Expr::app(format!(".{i}"), args),
            _ => Expr::app(head, args),
        }
    }

    pub(super) fn expr(&self, s: &Sexp) -> Expr {
        let items = match s {
            Sexp::Atom(a) => return Expr::sym(a.clone()),
            Sexp::List(items) => items,
        };
        let all = |args: &[Sexp]| args.iter().map(|a| self.expr(a)).collect::<Vec<_>>();
        match items.as_slice() {
            // An annotated term, `(! t :weight 0)`, is the term.
            [Sexp::Atom(head), term, ..] if head == "!" => self.expr(term),
            [Sexp::Atom(head), binds, body] if head == "let" => {
                let subst: HashMap<String, Expr> = bindings(binds)
                    .into_iter()
                    .map(|(name, value)| (name, self.expr(value)))
                    .collect();
                self.expr(body).subst(&subst)
            }
            [Sexp::Atom(head), binds, body] if head == "forall" || head == "exists" => {
                // A variable z3 binds in its answer stands for nothing in the program:
                // `__tmp_z3_model_<its name>`.
                let bound = bindings(binds);
                let renamed: HashMap<String, Expr> = bound
                    .iter()
                    .map(|(name, _)| (name.clone(), Expr::sym(z3_bound_name(name))))
                    .collect();
                let vars = bound
                    .into_iter()
                    .map(|(name, sort)| (z3_bound_name(&name), self.sort(sort)))
                    .collect();
                let q = if head == "forall" { "forall" } else { "exists" };
                Expr::Quant(q, vars, Box::new(self.expr(body).subst(&renamed)))
            }
            [Sexp::Atom(head), args @ ..] => self.applied(head, all(args)),
            [Sexp::List(head), args @ ..] => match head.as_slice() {
                [Sexp::Atom(u), Sexp::Atom(is), Sexp::Atom(ctor)] if u == "_" && is == "is" => {
                    Expr::app(format!("is_{ctor}"), all(args))
                }
                _ => Expr::app(self.sort(&Sexp::List(head.clone())), all(args)),
            },
            [] => Expr::sym("()"),
        }
    }
}

/// `s` as SMT-LIB text.
fn smt_text(s: &Sexp) -> String {
    match s {
        Sexp::Atom(a) => a.clone(),
        Sexp::List(items) => {
            let items: Vec<String> = items.iter().map(smt_text).collect();
            format!("({})", items.join(" "))
        }
    }
}

/// The formula `z3` prints after `(apply ...)`: the disjunction of its goals, each the
/// conjunction of its formulas. `None` when the text holds an error or no goals.
pub fn read_goals(text: &str, symbols: &Symbols) -> Option<Expr> {
    if text.contains("(error") {
        return None;
    }
    let tokens = tokens(text);
    let mut pos = 0;
    while let Some(sexp) = parse(&tokens, &mut pos) {
        let Sexp::List(items) = sexp else {
            continue;
        };
        let [Sexp::Atom(head), goals @ ..] = items.as_slice() else {
            continue;
        };
        if head != "goals" {
            continue;
        }
        let disjuncts: Vec<Expr> = goals
            .iter()
            .filter_map(|goal| match goal {
                Sexp::List(parts) if matches!(parts.first(), Some(Sexp::Atom(g)) if g == "goal") => {
                    let formulas = parts[1..]
                        .iter()
                        .take_while(|p| !matches!(p, Sexp::Atom(a) if a.starts_with(':')))
                        .map(|f| symbols.expr(f))
                        .collect();
                    Some(Expr::and(formulas))
                }
                _ => None,
            })
            .collect();
        return match disjuncts.len() {
            0 => Some(Expr::sym("false")),
            1 => disjuncts.into_iter().next(),
            _ => Some(Expr::app("or", disjuncts)),
        };
    }
    None
}

/// The interpretation of one predicate variable: its parameters and its body over them.
#[derive(Debug, Clone)]
pub struct Interpretation {
    pub params: Vec<String>,
    pub body: Expr,
    /// The parameters with their sorts and the body as the solver printed them, to give back to
    /// it (see [`super::simplify`]).
    pub source: Option<(Vec<(String, String)>, String)>,
}

impl Interpretation {
    /// The body with the parameters replaced by `args`.
    pub fn apply(&self, args: &[Expr]) -> Expr {
        let subst = self
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        self.body.subst(&subst).normalize()
    }
}

/// The `define-fun`s of a model as `z3` prints it after `(get-model)`, by name.
pub fn read(model: &str, symbols: &Symbols) -> HashMap<String, Interpretation> {
    let tokens = tokens(model);
    let mut pos = 0;
    let Some(Sexp::List(items)) = parse(&tokens, &mut pos) else {
        return HashMap::new();
    };
    // Some versions print `(model (define-fun ...) ...)`.
    let items = match items.first() {
        Some(Sexp::Atom(a)) if a == "model" => &items[1..],
        _ => &items[..],
    };
    items
        .iter()
        .filter_map(|item| match item {
            Sexp::List(parts) => match parts.as_slice() {
                [Sexp::Atom(def), Sexp::Atom(name), params, _, body] if def == "define-fun" => {
                    let typed: Vec<(String, String)> = bindings(params)
                        .into_iter()
                        .map(|(p, sort)| (p, smt_text(sort)))
                        .collect();
                    let interpretation = Interpretation {
                        params: typed.iter().map(|(p, _)| p.clone()).collect(),
                        body: symbols.expr(body),
                        source: Some((typed, smt_text(body))),
                    };
                    Some((name.clone(), interpretation))
                }
                _ => None,
            },
            _ => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_define_funs() {
        let model = "(\n  (define-fun p0 ((x!0 Int) (x!1 Int)) Bool\n    (let ((a!1 (+ x!1 1))) (and (>= x!0 0) (= x!0 a!1))))\n  (define-fun p1 () Bool true)\n)";
        let model = read(model, &Symbols::default());
        let p0 = &model["p0"];
        assert_eq!(p0.params, vec!["x!0", "x!1"]);
        let applied = p0.apply(&[Expr::sym("result"), Expr::sym("x")]);
        assert_eq!(applied.to_string(), "result >= 0 && result == x + 1");
        assert!(model["p1"].body.is_true());
    }

    #[test]
    fn reads_annotated_terms_as_the_term() {
        let model =
            "((define-fun p0 ((x!0 Int)) Bool (exists ((y Int)) (! (= x!0 (* 2 y)) :weight 0))))";
        let applied = read(model, &Symbols::default())["p0"].apply(&[Expr::sym("n")]);
        assert_eq!(
            applied.to_string(),
            "exists(|__tmp_z3_model_y: Int| n == 2 * __tmp_z3_model_y)"
        );
    }

    #[test]
    fn reads_the_goals_of_a_tactic() {
        let text = "(goals\n(goal\n  (>= x!0 2)\n  (= x!1 x!0)\n  :precision precise :depth 3)\n)";
        assert_eq!(
            read_goals(text, &Symbols::default()).unwrap().to_string(),
            "x!0 >= 2 && x!1 == x!0"
        );
        assert!(read_goals(
            "(error \"unknown constant foo\")\n(goals\n(goal\n :depth 1)\n)",
            &Symbols::default()
        )
        .is_none());
    }

    #[test]
    fn reads_reference_selectors() {
        let model = "((define-fun p2 ((x!0 A0_Mut<Int>)) Bool (= (mut_final<Int> x!0) (+ (mut_current<Int> x!0) 1))))";
        let symbols = Symbols::new(vec![
            ("mut_current<Int>".to_owned(), DeclaredSymbol::Current),
            ("mut_final<Int>".to_owned(), DeclaredSymbol::Final),
        ]);
        let model = read(model, &symbols);
        let applied = model["p2"].apply(&[Expr::sym("r")]);
        assert_eq!(applied.to_string(), "!r == *r + 1");
    }
}
