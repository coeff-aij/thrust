//! A solver's answers read back into terms and formulas: the inverse of [`super::smtlib2`] for
//! the symbols the query declares (see [`DeclaredSymbol`]) and the functions and predicates
//! Thrust knows ([`Function::ALL`], [`KnownPred::ALL`]).

use std::collections::HashMap;

use num_bigint::BigInt;

use super::format_context::DeclaredSymbol;
use super::sexp::Sexp;
use super::*;

/// What the symbols of a query stand for: those it declares for datatypes and its predicate
/// variables.
#[derive(Debug, Default)]
pub struct Symbols {
    declared: HashMap<String, DeclaredSymbol>,
    preds: HashMap<String, PredVarId>,
    /// The user-defined predicates and functions, by their name in the query.
    user_defined: HashMap<String, UserDefinedPred>,
}

impl Symbols {
    /// The symbols of the query `system.smtlib2(capabilities)` writes.
    pub fn of(system: &System, capabilities: Capabilities) -> Self {
        let mut symbols = Symbols::new(
            system.declared_symbols(capabilities),
            system.pred_vars.indices(),
        );
        symbols.user_defined = system
            .user_defined_pred_defs
            .iter()
            .map(|def| (def.symbol.to_string(), def.symbol.clone()))
            .collect();
        symbols
    }

    pub fn new(
        declared: Vec<(String, DeclaredSymbol)>,
        preds: impl IntoIterator<Item = PredVarId>,
    ) -> Self {
        Symbols {
            declared: declared.into_iter().collect(),
            preds: preds.into_iter().map(|p| (p.to_string(), p)).collect(),
            user_defined: HashMap::new(),
        }
    }

    /// The predicate variable the query names `name`.
    pub fn pred(&self, name: &str) -> Option<PredVarId> {
        self.preds.get(name).copied()
    }

    /// The term `s`, each free symbol a variable made by `var`.
    pub fn term<V: Clone>(&self, s: &Sexp, var: fn(&str) -> V) -> Term<V> {
        Reader::new(self, var).term(s)
    }

    /// The formula `s`, each free symbol a variable made by `var`.
    pub fn formula<V: Clone>(&self, s: &Sexp, var: fn(&str) -> V) -> Formula<V> {
        Reader::new(self, var).formula(s)
    }
}

/// `s` with each name a `let` binds replaced by what it binds.
fn expand(s: &Sexp, env: &HashMap<&str, Sexp>) -> Sexp {
    match s {
        Sexp::Atom(a) => env.get(a.as_str()).cloned().unwrap_or_else(|| s.clone()),
        Sexp::List(items) => match items.as_slice() {
            [Sexp::Atom(head), binds, body] if head == "let" => {
                let mut inner = env.clone();
                for (name, value) in binds.bindings() {
                    inner.insert(name, expand(value, env));
                }
                expand(body, &inner)
            }
            _ => Sexp::List(items.iter().map(|i| expand(i, env)).collect()),
        },
    }
}

/// A function the reader has no term for, applied by its name.
fn unknown<V>(name: &str, args: Vec<Term<V>>) -> Term<V> {
    Term::UserDefinedFn(UserDefinedPred::new(name.to_owned()), Sort::Null, args)
}

/// The formula that the Boolean term `t` holds.
fn holds<V>(t: Term<V>) -> Formula<V> {
    Atom::new(KnownPred::EQUAL.into(), vec![t, Term::Bool(true)]).into()
}

/// Reads one answer, numbering the variables its quantifiers bind.
struct Reader<'a, V> {
    symbols: &'a Symbols,
    var: fn(&str) -> V,
    bound: HashMap<String, (UserQuantifiedVarId, Sort)>,
    next: usize,
}

impl<'a, V: Clone> Reader<'a, V> {
    fn new(symbols: &'a Symbols, var: fn(&str) -> V) -> Self {
        Reader {
            symbols,
            var,
            bound: HashMap::new(),
            next: 0,
        }
    }

    fn sort(&self, s: &Sexp) -> Sort {
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
                _ => unimplemented!("an answer over the sort `{s}`"),
            },
        }
    }

    /// The variables `binds` binds, numbered, for the body of a quantifier; `leave` forgets them.
    fn enter(&mut self, binds: &Sexp) -> Vec<(UserQuantifiedVarId, Sort)> {
        binds
            .bindings()
            .into_iter()
            .map(|(name, sort)| {
                let var = (UserQuantifiedVarId::from_usize(self.next), self.sort(sort));
                self.next += 1;
                self.bound.insert(name.to_owned(), var.clone());
                var
            })
            .collect()
    }

    fn leave(&mut self, binds: &Sexp) {
        for (name, _) in binds.bindings() {
            self.bound.remove(name);
        }
    }

    fn symbol(&self, a: &str) -> Term<V> {
        if let Ok(n) = a.parse::<BigInt>() {
            return Term::Int(n);
        }
        if let Some((var, sort)) = self.bound.get(a) {
            return Term::UserQuantifiedVar(sort.clone(), *var);
        }
        // The constructor of the empty tuple is a constant.
        if let Some(DeclaredSymbol::TupleCtor) = self.symbols.declared.get(a) {
            return Term::Tuple(Vec::new());
        }
        match a {
            "true" => Term::Bool(true),
            "false" => Term::Bool(false),
            _ if a.starts_with('"') => Term::String(a.trim_matches('"').to_owned()),
            _ => Term::Var((self.var)(a)),
        }
    }

    fn term(&mut self, s: &Sexp) -> Term<V> {
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
                unknown(&head.to_string(), args)
            }
            [] => unknown("()", Vec::new()),
        }
    }

    /// `head` applied to `args`: a constructor or a selector of a `Box`, a `Mut` or a tuple, a
    /// function Thrust knows, or else a function by its name.
    fn applied(&self, head: &str, mut args: Vec<Term<V>>) -> Term<V> {
        let arg = |args: &mut Vec<Term<V>>| Box::new(args.remove(0));
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
        if let Some(symbol) = self.symbols.user_defined.get(head) {
            return Term::UserDefinedFn(symbol.clone(), Sort::Null, args);
        }
        let Some(f) = Function::named(head, args.len()) else {
            return unknown(head, args);
        };
        if !f.is_infix() {
            return Term::App(f, args);
        }
        // Thrust's infix functions take two arguments; the solver's take any number.
        args.into_iter()
            .reduce(|a, b| Term::App(f, vec![a, b]))
            .unwrap()
    }

    fn formula(&mut self, s: &Sexp) -> Formula<V> {
        let items = match s {
            Sexp::Atom(a) if a == "true" => return Formula::top(),
            Sexp::Atom(a) if a == "false" => return Formula::bottom(),
            Sexp::Atom(a) => match self.symbols.pred(a) {
                Some(p) => return Atom::new(p.into(), Vec::new()).into(),
                None => return holds(self.term(s)),
            },
            Sexp::List(items) => items,
        };
        let (head, args) = match items.as_slice() {
            [Sexp::Atom(head), args @ ..] => (head.as_str(), args),
            [Sexp::List(head), x] => match head.as_slice() {
                [Sexp::Atom(u), Sexp::Atom(is), Sexp::Atom(ctor)] if u == "_" && is == "is" => {
                    let tester = Pred::Tester(DatatypeSymbol::new(ctor.clone()));
                    return Atom::new(tester, vec![self.term(x)]).into();
                }
                _ => return holds(self.term(s)),
            },
            _ => return holds(self.term(s)),
        };
        let mut all = |fs: &[Sexp]| fs.iter().map(|f| self.formula(f)).collect::<Vec<_>>();
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
                Atom::new(KnownPred::NOT_EQUAL.into(), args).into()
            }
            (op, terms) if terms.len() >= 2 && KnownPred::named(op).is_some() => {
                let pred = KnownPred::named(op).unwrap();
                let terms: Vec<Term<V>> = terms.iter().map(|t| self.term(t)).collect();
                // A chain `(<= a b c)` compares each two neighbours.
                Formula::And(
                    terms
                        .windows(2)
                        .map(|w| Atom::new(pred.into(), w.to_vec()).into())
                        .collect(),
                )
            }
            (name, args) => {
                let pred: Pred =
                    match (self.symbols.pred(name), self.symbols.user_defined.get(name)) {
                        (Some(p), _) => p.into(),
                        (None, Some(symbol)) => symbol.clone().into(),
                        (None, None) => return holds(self.term(s)),
                    };
                let args = args.iter().map(|a| self.term(a)).collect();
                Atom::new(pred, args).into()
            }
        }
    }
}

/// The formula `z3` prints after `(apply ...)`, among `printed`: the disjunction of its goals,
/// each the conjunction of its formulas. `None` when the solver printed an error or no goals.
pub fn goals<V: Clone>(
    printed: &[Sexp],
    symbols: &Symbols,
    var: fn(&str) -> V,
) -> Option<Formula<V>> {
    if printed.iter().any(Sexp::is_error) {
        return None;
    }
    let goals = printed.iter().find_map(|s| match s {
        Sexp::List(items) if items.first().and_then(Sexp::atom) == Some("goals") => {
            Some(&items[1..])
        }
        _ => None,
    })?;
    let disjuncts = goals
        .iter()
        .filter_map(|goal| match goal {
            Sexp::List(parts) if parts.first().and_then(Sexp::atom) == Some("goal") => {
                let formulas = parts[1..]
                    .iter()
                    .take_while(|p| !p.atom().is_some_and(|a| a.starts_with(':')))
                    .map(|f| symbols.formula(f, var))
                    .collect();
                Some(Formula::And(formulas))
            }
            _ => None,
        })
        .collect();
    let mut f = Formula::Or(disjuncts);
    f.simplify();
    Some(f)
}

/// A function a model defines: its parameters and its body over them.
#[derive(Debug, Clone)]
pub struct Definition<V> {
    pub params: Vec<V>,
    pub body: Formula<V>,
    /// The parameters with their sorts and the body as the solver printed them.
    pub source: (Vec<(String, String)>, String),
}

impl<V: Clone + PartialEq> Definition<V> {
    /// The body with the parameters replaced by `args`.
    pub fn apply(&self, args: &[Term<V>]) -> Formula<V> {
        self.body
            .clone()
            .subst_var(|v| match self.params.iter().position(|p| *p == v) {
                Some(k) => args[k].clone(),
                None => Term::Var(v),
            })
    }
}

/// The `define-fun`s of a model as `z3` prints it after `(get-model)`, by name.
pub fn definitions<V: Clone>(
    model: &Sexp,
    symbols: &Symbols,
    var: fn(&str) -> V,
) -> HashMap<String, Definition<V>> {
    let Sexp::List(items) = model else {
        return HashMap::new();
    };
    // Some versions print `(model (define-fun ...) ...)`.
    let items = match items.first().and_then(Sexp::atom) {
        Some("model") => &items[1..],
        _ => &items[..],
    };
    items
        .iter()
        .filter_map(|item| match item {
            Sexp::List(parts) => match parts.as_slice() {
                [Sexp::Atom(def), Sexp::Atom(name), params, _, body] if def == "define-fun" => {
                    let typed: Vec<(String, String)> = params
                        .bindings()
                        .into_iter()
                        .map(|(p, sort)| (p.to_owned(), sort.to_string()))
                        .collect();
                    let definition = Definition {
                        params: typed.iter().map(|(p, _)| var(p)).collect(),
                        body: symbols.formula(body, var),
                        source: (typed, body.to_string()),
                    };
                    Some((name.clone(), definition))
                }
                _ => None,
            },
            Sexp::Atom(_) => None,
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct V(&'static str);

    impl std::fmt::Debug for V {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(self.0)
        }
    }

    fn v(s: &str) -> V {
        V(Box::leak(s.to_owned().into_boxed_str()))
    }

    fn model(text: &str) -> Sexp {
        sexp::parse_all(text).remove(0)
    }

    fn applied(model: &Sexp, symbols: &Symbols, pred: &str, args: &[&str]) -> String {
        let args: Vec<Term<V>> = args.iter().map(|a| Term::Var(v(a))).collect();
        let mut f = definitions(model, symbols, v)[pred].apply(&args);
        f.simplify();
        f.display().to_string()
    }

    #[test]
    fn reads_define_funs() {
        let m = model("(\n  (define-fun p0 ((x!0 Int) (x!1 Int)) Bool\n    (let ((a!1 (+ x!1 1))) (and (>= x!0 0) (= x!0 a!1))))\n  (define-fun p1 () Bool true)\n)");
        let symbols = Symbols::default();
        assert_eq!(
            applied(&m, &symbols, "p0", &["result", "x"]),
            "result >= 0 ∧ result = x + 1"
        );
        assert!(definitions(&m, &symbols, v)["p1"].body.is_top());
    }

    #[test]
    fn reads_annotated_terms_as_the_term() {
        let m = model(
            "((define-fun p0 ((x!0 Int)) Bool (exists ((y Int)) (! (= x!0 (* 2 y)) :weight 0))))",
        );
        assert_eq!(
            applied(&m, &Symbols::default(), "p0", &["n"]),
            "∃q$0: int. n = 2 * q$0"
        );
    }

    #[test]
    fn reads_the_goals_of_a_tactic() {
        let printed = sexp::parse_all(
            "(goals\n(goal\n  (>= x!0 2)\n  (= x!1 x!0)\n  :precision precise :depth 3)\n)",
        );
        let goals = goals(&printed, &Symbols::default(), v).unwrap();
        assert_eq!(goals.display().to_string(), "x!0 >= 2 ∧ x!1 = x!0");
        let failed =
            sexp::parse_all("(error \"unknown constant foo\")\n(goals\n(goal\n :depth 1)\n)");
        assert!(super::goals(&failed, &Symbols::default(), v).is_none());
    }

    #[test]
    fn reads_reference_selectors() {
        let m = model("((define-fun p2 ((x!0 A0_Mut<Int>)) Bool (= (mut_final<Int> x!0) (+ (mut_current<Int> x!0) 1))))");
        let symbols = Symbols::new(
            vec![
                ("mut_current<Int>".to_owned(), DeclaredSymbol::Current),
                ("mut_final<Int>".to_owned(), DeclaredSymbol::Final),
            ],
            [],
        );
        assert_eq!(applied(&m, &symbols, "p2", &["r"]), "°r = *r + 1");
    }
}
