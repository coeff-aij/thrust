//! The solver's answers read into Thrust's formulas (see [`super::formula`]): the interpretation
//! of each predicate variable in a model, and the formulas a tactic leaves.

use std::collections::HashMap;

use num_bigint::BigInt;

use super::formula::{comparison, Formula, Name, Term};
use crate::chc;
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

/// `s` with each name a `let` binds replaced by what it binds.
fn expand(s: &Sexp, env: &HashMap<String, Sexp>) -> Sexp {
    match s {
        Sexp::Atom(a) => env.get(a).cloned().unwrap_or_else(|| s.clone()),
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(head), binds, body] if head == "let" => {
                let mut inner = env.clone();
                for (name, value) in bindings(binds) {
                    inner.insert(name, expand(value, env));
                }
                expand(body, &inner)
            }
            _ => Sexp::List(items.iter().map(|i| expand(i, env)).collect()),
        },
    }
}

/// The functions of the solver's answers Thrust has a [`chc::Function`] for, by name; `-` of one
/// argument is [`chc::Function::NEG`].
const FUNCTIONS: &[chc::Function] = &[
    chc::Function::ADD,
    chc::Function::SUB,
    chc::Function::MUL,
    chc::Function::MOD,
    chc::Function::EUCLIDEAN_DIV,
    chc::Function::EQ,
    chc::Function::GE,
    chc::Function::GT,
    chc::Function::LE,
    chc::Function::LT,
    chc::Function::AND,
    chc::Function::OR,
    chc::Function::NOT,
    chc::Function::BVADD,
    chc::Function::BVSUB,
    chc::Function::BVMUL,
    chc::Function::BVAND,
    chc::Function::BVOR,
    chc::Function::BVXOR,
    chc::Function::BVSHL,
    chc::Function::BVLSHR,
    chc::Function::BVASHR,
    chc::Function::BVNOT,
    chc::Function::BVNEG,
    chc::Function::BVULT,
    chc::Function::BVULE,
    chc::Function::BVUGT,
    chc::Function::BVUGE,
    chc::Function::BVSLT,
    chc::Function::BVSLE,
    chc::Function::BVSGT,
    chc::Function::BVSGE,
    chc::Function::UBV_TO_INT,
    chc::Function::SBV_TO_INT,
    chc::Function::STORE,
    chc::Function::SELECT,
    chc::Function::SEQ_CONCAT,
    chc::Function::SEQ_EXTRACT,
    chc::Function::SEQ_LEN,
    chc::Function::SEQ_UNIT,
    chc::Function::SEQ_NTH,
    chc::Function::SEQ_STORE,
    chc::Function::ITE,
];

/// What the symbols of the query stand for, to read the solver's answers over them: those it
/// declares for datatypes (see `chc::System::declared_symbols`) and its predicate variables.
#[derive(Debug, Default)]
pub struct Symbols {
    declared: HashMap<String, DeclaredSymbol>,
    preds: HashMap<String, chc::PredVarId>,
}

impl Symbols {
    pub fn new(
        declared: Vec<(String, DeclaredSymbol)>,
        preds: impl IntoIterator<Item = chc::PredVarId>,
    ) -> Self {
        Symbols {
            declared: declared.into_iter().collect(),
            preds: preds.into_iter().map(|p| (p.to_string(), p)).collect(),
        }
    }

    /// The predicate variable the query names `name`.
    pub fn pred(&self, name: &str) -> Option<chc::PredVarId> {
        self.preds.get(name).copied()
    }

    pub(super) fn term(&self, s: &Sexp) -> Term {
        Reader::new(self).term(s)
    }

    pub(super) fn formula(&self, s: &Sexp) -> Formula {
        Reader::new(self).formula(s)
    }
}

/// Reads one answer, numbering the variables its quantifiers bind.
struct Reader<'a> {
    symbols: &'a Symbols,
    bound: HashMap<String, (chc::UserQuantifiedVarId, chc::Sort)>,
    next: usize,
}

impl<'a> Reader<'a> {
    fn new(symbols: &'a Symbols) -> Self {
        Reader {
            symbols,
            bound: HashMap::new(),
            next: 0,
        }
    }

    fn sort(&self, s: &Sexp) -> chc::Sort {
        use chc::Sort;
        let sort = |s| Box::new(self.sort(s));
        match s {
            Sexp::Atom(a) if a == "Int" => Sort::Int,
            Sexp::Atom(a) if a == "Bool" => Sort::Bool,
            Sexp::Atom(a) if a == "String" => Sort::String,
            Sexp::Atom(a) => match self.symbols.declared.get(a) {
                Some(DeclaredSymbol::Sort(sort)) => sort.clone(),
                _ => unimplemented!(
                    "an answer over the sort `{a}`, which the query does not declare"
                ),
            },
            Sexp::List(items) => match items.as_slice() {
                [Sexp::Atom(u), Sexp::Atom(bv), Sexp::Atom(w)] if u == "_" && bv == "BitVec" => {
                    Sort::BitVec {
                        width: w.parse().unwrap(),
                    }
                }
                [Sexp::Atom(seq), s] if seq == "Seq" => Sort::Seq(sort(s)),
                [Sexp::Atom(array), k, v] if array == "Array" => Sort::Array(sort(k), sort(v)),
                _ => unimplemented!("an answer over the sort `{}`", smt_text(s)),
            },
        }
    }

    /// The variables `binds` binds, numbered, for the body of a quantifier; `leave` forgets them.
    fn enter(&mut self, binds: &Sexp) -> Vec<(chc::UserQuantifiedVarId, chc::Sort)> {
        bindings(binds)
            .into_iter()
            .map(|(name, sort)| {
                let var = (
                    chc::UserQuantifiedVarId::from_usize(self.next),
                    self.sort(sort),
                );
                self.next += 1;
                self.bound.insert(name, var.clone());
                var
            })
            .collect()
    }

    fn leave(&mut self, binds: &Sexp) {
        for (name, _) in bindings(binds) {
            self.bound.remove(&name);
        }
    }

    fn symbol(&self, a: &str) -> Term {
        if let Ok(n) = a.parse::<BigInt>() {
            return Term::Int(n);
        }
        if let Some((var, sort)) = self.bound.get(a) {
            return Term::UserQuantifiedVar(sort.clone(), *var);
        }
        match a {
            "true" => Term::Bool(true),
            "false" => Term::Bool(false),
            _ if a.starts_with('"') => Term::String(a.trim_matches('"').to_owned()),
            _ => Term::Var(Name::new(a)),
        }
    }

    fn term(&mut self, s: &Sexp) -> Term {
        let items = match s {
            Sexp::Atom(a) => return self.symbol(a),
            Sexp::List(items) => items,
        };
        match items.as_slice() {
            // An annotated term, `(! t :weight 0)`, is the term.
            [Sexp::Atom(head), term, ..] if head == "!" => self.term(term),
            [Sexp::Atom(head), _, _] if head == "let" => self.term(&expand(s, &HashMap::new())),
            [Sexp::Atom(head), Sexp::Atom(n)] if head == "-" && n.parse::<BigInt>().is_ok() => {
                Term::Int(-n.parse::<BigInt>().unwrap())
            }
            [Sexp::Atom(head), args @ ..] => {
                let args = args.iter().map(|a| self.term(a)).collect();
                self.applied(head, args)
            }
            [head, args @ ..] => {
                let args = args.iter().map(|a| self.term(a)).collect();
                unknown(&smt_text(head), args)
            }
            [] => unknown("()", Vec::new()),
        }
    }

    /// `head` applied to `args`: a constructor or a selector of a `Box`, a `Mut` or a tuple, a
    /// function Thrust knows, or else a function by its name.
    fn applied(&self, head: &str, mut args: Vec<Term>) -> Term {
        let arg = |args: &mut Vec<Term>| Box::new(args.remove(0));
        match (self.symbols.declared.get(head), args.len()) {
            (Some(DeclaredSymbol::BoxCtor), 1) => return Term::Box(arg(&mut args)),
            (Some(DeclaredSymbol::MutCtor), 2) => {
                let current = arg(&mut args);
                return Term::Mut(current, arg(&mut args));
            }
            (Some(DeclaredSymbol::TupleCtor), _) => return Term::Tuple(args),
            (Some(DeclaredSymbol::Current), 1) => return Term::MutCurrent(arg(&mut args)),
            (Some(DeclaredSymbol::Final), 1) => return Term::MutFinal(arg(&mut args)),
            (Some(DeclaredSymbol::Field(i)), 1) => return Term::TupleProj(arg(&mut args), *i),
            _ => {}
        }
        if head == "-" && args.len() == 1 {
            return Term::App(chc::Function::NEG, args);
        }
        let Some(f) = FUNCTIONS.iter().find(|f| f.name() == head) else {
            return unknown(head, args);
        };
        if !f.is_infix() {
            return Term::App(*f, args);
        }
        // Thrust's infix functions take two arguments; the solver's take any number.
        args.into_iter()
            .reduce(|a, b| Term::App(*f, vec![a, b]))
            .unwrap()
    }

    fn formula(&mut self, s: &Sexp) -> Formula {
        let items = match s {
            Sexp::Atom(a) if a == "true" => return Formula::top(),
            Sexp::Atom(a) if a == "false" => return Formula::bottom(),
            Sexp::Atom(a) => match self.symbols.pred(a) {
                Some(p) => return chc::Atom::new(p.into(), Vec::new()).into(),
                None => return holds(self.term(s)),
            },
            Sexp::List(items) => items,
        };
        let mut all = |fs: &[Sexp]| fs.iter().map(|f| self.formula(f)).collect::<Vec<_>>();
        let (head, args) = match items.as_slice() {
            [Sexp::Atom(head), args @ ..] => (head.as_str(), args),
            [Sexp::List(head), x] => match head.as_slice() {
                [Sexp::Atom(u), Sexp::Atom(is), Sexp::Atom(ctor)] if u == "_" && is == "is" => {
                    let tester = chc::Pred::Tester(chc::DatatypeSymbol::new(ctor.clone()));
                    return chc::Atom::new(tester, vec![self.term(x)]).into();
                }
                _ => return holds(self.term(s)),
            },
            _ => return holds(self.term(s)),
        };
        match (head, args) {
            ("!", [f, ..]) => self.formula(f),
            ("let", [_, _]) => self.formula(&expand(s, &HashMap::new())),
            ("and", fs) => Formula::And(all(fs)),
            ("or", fs) => Formula::Or(all(fs)),
            ("not", [f]) => self.formula(f).not(),
            ("=>", fs) => all(fs)
                .into_iter()
                .rev()
                .reduce(|b, a| a.implies(b))
                .unwrap(),
            ("ite", [c, a, b]) => {
                let (c, a, b) = (self.formula(c), self.formula(a), self.formula(b));
                Formula::Or(vec![
                    Formula::And(vec![c.clone(), a]),
                    Formula::And(vec![c.not(), b]),
                ])
            }
            ("forall" | "exists", [binds, body]) => {
                let vars = self.enter(binds);
                let body = Box::new(self.formula(body));
                self.leave(binds);
                match head {
                    "forall" => Formula::Forall(vars, body),
                    _ => Formula::Exists(vars, body),
                }
            }
            ("distinct", [a, b]) => {
                let args = vec![self.term(a), self.term(b)];
                chc::Atom::new(chc::KnownPred::NOT_EQUAL.into(), args).into()
            }
            (op, terms) if terms.len() >= 2 && comparison(op).is_some() => {
                let pred = comparison(op).unwrap();
                let terms: Vec<Term> = terms.iter().map(|t| self.term(t)).collect();
                // A chain `(<= a b c)` compares each two neighbours.
                Formula::And(
                    terms
                        .windows(2)
                        .map(|w| chc::Atom::new(pred.into(), w.to_vec()).into())
                        .collect(),
                )
            }
            (name, args) => match self.symbols.pred(name) {
                Some(p) => {
                    let args = args.iter().map(|a| self.term(a)).collect();
                    chc::Atom::new(p.into(), args).into()
                }
                None => holds(self.term(s)),
            },
        }
    }
}

/// A function the report has no form for, applied by its name.
fn unknown(name: &str, args: Vec<Term>) -> Term {
    let f = chc::UserDefinedPred::new(name.to_owned());
    Term::UserDefinedFn(f, chc::Sort::Null, args)
}

/// The formula that the Boolean term `t` holds.
fn holds(t: Term) -> Formula {
    chc::Atom::new(chc::KnownPred::EQUAL.into(), vec![t, Term::Bool(true)]).into()
}

/// The formula `z3` prints after `(apply ...)`: the disjunction of its goals, each the
/// conjunction of its formulas. `None` when the text holds an error or no goals.
pub fn read_goals(text: &str, symbols: &Symbols) -> Option<Formula> {
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
        let disjuncts = goals
            .iter()
            .filter_map(|goal| match goal {
                Sexp::List(parts) if matches!(parts.first(), Some(Sexp::Atom(g)) if g == "goal") => {
                    let formulas = parts[1..]
                        .iter()
                        .take_while(|p| !matches!(p, Sexp::Atom(a) if a.starts_with(':')))
                        .map(|f| symbols.formula(f))
                        .collect();
                    Some(Formula::And(formulas))
                }
                _ => None,
            })
            .collect();
        let mut f = Formula::Or(disjuncts);
        f.simplify();
        return Some(f);
    }
    None
}

/// The interpretation of one predicate variable: its parameters and its body over them.
#[derive(Debug, Clone)]
pub struct Interpretation {
    pub params: Vec<Name>,
    pub body: Formula,
    /// The parameters with their sorts and the body as the solver printed them, to give back to
    /// it (see [`super::simplify`]).
    pub source: (Vec<(String, String)>, String),
}

impl Interpretation {
    /// The body with the parameters replaced by `args`.
    pub fn apply(&self, args: &[Term]) -> Formula {
        self.body
            .clone()
            .subst_var(|v| match self.params.iter().position(|p| *p == v) {
                Some(k) => args[k].clone(),
                None => Term::Var(v),
            })
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
                        params: typed.iter().map(|(p, _)| Name::new(p)).collect(),
                        body: symbols.formula(body),
                        source: (typed, smt_text(body)),
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
    use crate::report::formula::OneLine as _;

    fn applied(model: &str, symbols: &Symbols, name: &str, args: &[&str]) -> String {
        let args: Vec<Term> = args.iter().map(|a| Term::Var(Name::new(a))).collect();
        let mut f = read(model, symbols)[name].apply(&args);
        f.simplify();
        f.one_line()
    }

    #[test]
    fn reads_define_funs() {
        let model = "(\n  (define-fun p0 ((x!0 Int) (x!1 Int)) Bool\n    (let ((a!1 (+ x!1 1))) (and (>= x!0 0) (= x!0 a!1))))\n  (define-fun p1 () Bool true)\n)";
        let symbols = Symbols::default();
        assert_eq!(
            applied(model, &symbols, "p0", &["result", "x"]),
            "result >= 0∧ result = (x + 1)"
        );
        assert!(read(model, &symbols)["p1"].body.is_top());
    }

    #[test]
    fn reads_annotated_terms_as_the_term() {
        let model =
            "((define-fun p0 ((x!0 Int)) Bool (exists ((y Int)) (! (= x!0 (* 2 y)) :weight 0))))";
        assert_eq!(
            applied(model, &Symbols::default(), "p0", &["n"]),
            "∃q$0: int. n = (2 * q$0)"
        );
    }

    #[test]
    fn reads_the_goals_of_a_tactic() {
        let text = "(goals\n(goal\n  (>= x!0 2)\n  (= x!1 x!0)\n  :precision precise :depth 3)\n)";
        let goals = read_goals(text, &Symbols::default()).unwrap();
        assert_eq!(goals.one_line(), "x!0 >= 2∧ x!1 = x!0");
        assert!(read_goals(
            "(error \"unknown constant foo\")\n(goals\n(goal\n :depth 1)\n)",
            &Symbols::default()
        )
        .is_none());
    }

    #[test]
    fn reads_reference_selectors() {
        let model = "((define-fun p2 ((x!0 A0_Mut<Int>)) Bool (= (mut_final<Int> x!0) (+ (mut_current<Int> x!0) 1))))";
        let symbols = Symbols::new(
            vec![
                ("mut_current<Int>".to_owned(), DeclaredSymbol::Current),
                ("mut_final<Int>".to_owned(), DeclaredSymbol::Final),
            ],
            [],
        );
        assert_eq!(applied(model, &symbols, "p2", &["r"]), "°r = (*r + 1)");
    }
}
