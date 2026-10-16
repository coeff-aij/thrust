//! Formulas as the report prints them.
//!
//! An [`Expr`] is an SMT-LIB-shaped tree: Thrust's own terms and formulas are read into it with
//! the SMT-LIB names of their functions, and so is a solver's model, so one printer shows both in
//! the syntax of the annotations (`&&`, `==>`, `*x` and `!x` of a `&mut`, `result`).

use std::collections::HashMap;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Sym(String),
    App(String, Vec<Expr>),
    Quant(&'static str, Vec<(String, String)>, Box<Expr>),
}

impl Expr {
    pub fn sym(s: impl Into<String>) -> Expr {
        Expr::Sym(s.into())
    }

    pub fn app(f: impl Into<String>, args: Vec<Expr>) -> Expr {
        Expr::App(f.into(), args)
    }

    pub fn tt() -> Expr {
        Expr::sym("true")
    }

    pub fn is_true(&self) -> bool {
        matches!(self, Expr::Sym(s) if s == "true")
    }

    pub fn is_false(&self) -> bool {
        matches!(self, Expr::Sym(s) if s == "false")
    }

    /// The conjunction of `es`, without the `true`s among them.
    pub fn and(es: Vec<Expr>) -> Expr {
        let mut conjuncts: Vec<Expr> = es.into_iter().flat_map(Expr::into_conjuncts).collect();
        conjuncts.retain(|e| !e.is_true());
        match conjuncts.len() {
            0 => Expr::tt(),
            1 => conjuncts.pop().unwrap(),
            _ => Expr::app("and", conjuncts),
        }
    }

    pub fn into_conjuncts(self) -> Vec<Expr> {
        match self {
            Expr::App(f, args) if f == "and" => {
                args.into_iter().flat_map(Expr::into_conjuncts).collect()
            }
            e if e.is_true() => vec![],
            e => vec![e],
        }
    }

    /// Replaces each symbol `s` that `subst` maps by its image.
    pub fn subst(&self, subst: &HashMap<String, Expr>) -> Expr {
        match self {
            Expr::Sym(s) => subst.get(s).cloned().unwrap_or_else(|| self.clone()),
            Expr::App(f, args) => {
                Expr::App(f.clone(), args.iter().map(|a| a.subst(subst)).collect())
            }
            Expr::Quant(q, vars, body) => {
                let mut inner = subst.clone();
                for (v, _) in vars {
                    inner.remove(v);
                }
                Expr::Quant(q, vars.clone(), Box::new(body.subst(&inner)))
            }
        }
    }

    pub fn mentions(&self, sym: &str) -> bool {
        self.count(sym) > 0
    }

    pub fn count(&self, sym: &str) -> usize {
        match self {
            Expr::Sym(s) => usize::from(s == sym),
            Expr::App(_, args) => args.iter().map(|a| a.count(sym)).sum(),
            Expr::Quant(_, vars, body) if vars.iter().all(|(v, _)| v != sym) => body.count(sym),
            Expr::Quant(..) => 0,
        }
    }
}

impl Expr {
    /// Rewrites what reads as noise into an equivalent formula: the current and final values of a
    /// `Mut::new(c, f)` are `c` and `f`, two such pairs are equal when their components are, a
    /// comparison with `true` or `false` is the formula or its negation, a negated comparison is
    /// the opposite comparison, and `-1 * x` and `a + -b` are `-x` and `a - b`.
    pub fn normalize(self) -> Expr {
        let e = match self {
            Expr::App(f, args) => Expr::App(f, args.into_iter().map(Expr::normalize).collect()),
            Expr::Quant(q, vars, body) => Expr::Quant(q, vars, Box::new(body.normalize())),
            e => e,
        };
        let Expr::App(f, args) = e else {
            return e;
        };
        let negated = |op: &str| match op {
            "<" => Some(">="),
            "<=" => Some(">"),
            ">" => Some("<="),
            ">=" => Some("<"),
            _ => None,
        };
        let minus_one = |e: &Expr| *e == Expr::app("-", vec![Expr::sym("1")]);
        match (f.as_str(), args.as_slice()) {
            ("not", [Expr::App(op, xs)]) if xs.len() == 2 && negated(op).is_some() => {
                Expr::app(negated(op).unwrap(), xs.clone())
            }
            ("*", [m, x]) | ("*", [x, m]) if minus_one(m) => Expr::app("-", vec![x.clone()]),
            ("+", xs)
                if xs.len() >= 2
                    && xs[1..]
                        .iter()
                        .any(|x| matches!(x, Expr::App(n, ys) if n == "-" && ys.len() == 1)) =>
            {
                let mut sum = xs[0].clone();
                for x in &xs[1..] {
                    sum = match x {
                        Expr::App(n, ys) if n == "-" && ys.len() == 1 => {
                            Expr::app("-", vec![sum, ys[0].clone()])
                        }
                        x => Expr::app("+", vec![sum, x.clone()]),
                    };
                }
                sum
            }
            ("deref", [Expr::App(m, xs)]) if m == "Mut::new" && xs.len() == 2 => xs[0].clone(),
            ("final", [Expr::App(m, xs)]) if m == "Mut::new" && xs.len() == 2 => xs[1].clone(),
            ("=", [Expr::App(m1, xs), Expr::App(m2, ys)])
                if m1 == "Mut::new" && m2 == "Mut::new" && xs.len() == 2 && ys.len() == 2 =>
            {
                Expr::and(vec![
                    Expr::app("=", vec![xs[0].clone(), ys[0].clone()]),
                    Expr::app("=", vec![xs[1].clone(), ys[1].clone()]),
                ])
            }
            ("=", [x, b]) | ("=", [b, x]) if b.is_true() => x.clone(),
            ("=", [x, b]) | ("=", [b, x]) if b.is_false() => {
                Expr::app("not", vec![x.clone()]).normalize()
            }
            ("not", [Expr::App(g, xs)]) if g == "not" && xs.len() == 1 => xs[0].clone(),
            _ => Expr::App(f, args),
        }
    }
}

/// Reads a term, naming each variable by `name`.
pub fn of_term<V: chc::Var>(term: &chc::Term<V>, name: &impl Fn(&V) -> String) -> Expr {
    use chc::Term;
    let all = |ts: &[Term<V>]| ts.iter().map(|t| of_term(t, name)).collect::<Vec<_>>();
    match term {
        Term::Var(v) => Expr::sym(name(v)),
        Term::Bool(b) => Expr::sym(b.to_string()),
        Term::Int(n) if n.sign() == num_bigint::Sign::Minus => {
            Expr::app("-", vec![Expr::sym((-n).to_string())])
        }
        Term::Int(n) => Expr::sym(n.to_string()),
        Term::String(s) => Expr::sym(format!("{s:?}")),
        // A `Box` is read as its content, as the solver is given it.
        Term::Box(t) | Term::BoxCurrent(t) => of_term(t, name),
        Term::Mut(c, f) => Expr::app("Mut::new", vec![of_term(c, name), of_term(f, name)]),
        Term::MutCurrent(t) => Expr::app("deref", vec![of_term(t, name)]),
        Term::MutFinal(t) => Expr::app("final", vec![of_term(t, name)]),
        Term::App(f, args) => Expr::app(f.name(), all(args)),
        Term::Tuple(ts) => Expr::app("tuple", all(ts)),
        Term::TupleProj(t, i) => Expr::app(format!(".{i}"), vec![of_term(t, name)]),
        Term::DatatypeCtor(_, sym, args) => Expr::app(sym.to_string(), all(args)),
        Term::DatatypeDiscr(_, t) => Expr::app("discriminant", vec![of_term(t, name)]),
        Term::UserDefinedFn(f, _, args) => Expr::app(f.to_string(), all(args)),
        Term::ForallFn(f, args) => Expr::app(f.to_string(), all(args)),
        Term::UserQuantifiedVar(_, id) => Expr::sym(id.to_string()),
        _ => Expr::sym(term.display().to_string()),
    }
}

/// Reads an atom, naming each predicate variable by `pred_name`.
pub fn of_atom<V: chc::Var>(
    atom: &chc::Atom<V>,
    name: &impl Fn(&V) -> String,
    pred_name: &impl Fn(chc::PredVarId) -> String,
) -> Expr {
    let args = atom.args.iter().map(|t| of_term(t, name)).collect();
    let applied = match &atom.pred {
        chc::Pred::Known(p) if p.is_top() => Expr::tt(),
        chc::Pred::Known(p) if p.is_bottom() => Expr::sym("false"),
        chc::Pred::Known(p) if p.is_negative() => Expr::app("not", vec![Expr::app(p.name(), args)]),
        chc::Pred::Known(p) => Expr::app(p.name(), args),
        chc::Pred::Var(p) => Expr::app(pred_name(*p), args),
        chc::Pred::Tester(c) => Expr::app(format!("is_{c}"), args),
        pred => Expr::app(pred.to_string(), args),
    };
    match &atom.guard {
        Some(guard) => Expr::app("=>", vec![of_formula(guard, name, pred_name), applied]),
        None => applied,
    }
}

pub fn of_formula<V: chc::Var>(
    formula: &chc::Formula<V>,
    name: &impl Fn(&V) -> String,
    pred_name: &impl Fn(chc::PredVarId) -> String,
) -> Expr {
    use chc::Formula;
    let all = |fs: &[Formula<V>]| {
        fs.iter()
            .map(|f| of_formula(f, name, pred_name))
            .collect::<Vec<_>>()
    };
    let binders = |vars: &[(chc::UserQuantifiedVarId, chc::Sort)]| {
        vars.iter()
            .map(|(v, s)| (v.to_string(), s.display().to_string()))
            .collect()
    };
    match formula {
        Formula::Atom(atom) => of_atom(atom, name, pred_name),
        Formula::Not(f) => Expr::app("not", vec![of_formula(f, name, pred_name)]),
        Formula::And(fs) => Expr::and(all(fs)),
        Formula::Or(fs) if fs.is_empty() => Expr::sym("false"),
        Formula::Or(fs) => Expr::app("or", all(fs)),
        Formula::Implies(a, b) => Expr::app(
            "=>",
            vec![
                of_formula(a, name, pred_name),
                of_formula(b, name, pred_name),
            ],
        ),
        Formula::Exists(vars, f) => Expr::Quant(
            "exists",
            binders(vars),
            Box::new(of_formula(f, name, pred_name)),
        ),
        Formula::Forall(vars, f) => Expr::Quant(
            "forall",
            binders(vars),
            Box::new(of_formula(f, name, pred_name)),
        ),
    }
}

/// Reads the conjunction of a clause body's atoms and formula.
pub fn of_body<V: chc::Var>(
    body: &chc::Body<V>,
    name: &impl Fn(&V) -> String,
    pred_name: &impl Fn(chc::PredVarId) -> String,
) -> Expr {
    let atoms = body.atoms.iter().map(|a| of_atom(a, name, pred_name));
    Expr::and(
        atoms
            .chain(std::iter::once(of_formula(&body.formula, name, pred_name)))
            .collect(),
    )
}

// Precedences, loosest first.
const IMPLIES: u8 = 1;
const OR: u8 = 2;
const AND: u8 = 3;
const CMP: u8 = 4;
const ADD: u8 = 5;
const MUL: u8 = 6;
const UNARY: u8 = 7;
const POSTFIX: u8 = 8;

fn infix(f: &str) -> Option<(&'static str, u8)> {
    Some(match f {
        "=>" => ("==>", IMPLIES),
        "or" => ("||", OR),
        "and" => ("&&", AND),
        "=" => ("==", CMP),
        "distinct" => ("!=", CMP),
        "<" => ("<", CMP),
        "<=" => ("<=", CMP),
        ">" => (">", CMP),
        ">=" => (">=", CMP),
        "+" => ("+", ADD),
        "-" => ("-", ADD),
        "*" => ("*", MUL),
        "div" => ("/", MUL),
        "mod" => ("%", MUL),
        _ => return None,
    })
}

impl Expr {
    fn prec(&self) -> u8 {
        match self {
            Expr::Sym(_) | Expr::Quant(..) => POSTFIX,
            Expr::App(f, args) => match (f.as_str(), args.len()) {
                ("not" | "-" | "deref" | "final", 1) => UNARY,
                ("ite", 3) => 0,
                (f, n) if n >= 2 => infix(f).map_or(POSTFIX, |(_, p)| p),
                _ => POSTFIX,
            },
        }
    }

    fn fmt_at(&self, f: &mut std::fmt::Formatter<'_>, min: u8) -> std::fmt::Result {
        if self.prec() < min {
            write!(f, "(")?;
            self.fmt_bare(f)?;
            return write!(f, ")");
        }
        self.fmt_bare(f)
    }

    fn fmt_bare(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (head, args) = match self {
            Expr::Sym(s) => return write!(f, "{s}"),
            Expr::Quant(q, vars, body) => {
                write!(f, "{q}(|")?;
                for (i, (v, s)) in vars.iter().enumerate() {
                    let sep = if i > 0 { ", " } else { "" };
                    write!(f, "{sep}{v}: {s}")?;
                }
                write!(f, "| ")?;
                body.fmt_at(f, 0)?;
                return write!(f, ")");
            }
            Expr::App(head, args) => (head.as_str(), args.as_slice()),
        };
        match (head, args) {
            ("not", [Expr::App(eq, xs)]) if eq == "=" && xs.len() == 2 => {
                xs[0].fmt_at(f, CMP + 1)?;
                write!(f, " != ")?;
                xs[1].fmt_at(f, CMP + 1)
            }
            ("not", [x]) => {
                write!(f, "!")?;
                x.fmt_at(f, UNARY)
            }
            ("-", [x]) => {
                write!(f, "-")?;
                x.fmt_at(f, UNARY)
            }
            ("deref", [x]) => {
                write!(f, "*")?;
                x.fmt_at(f, UNARY)
            }
            ("final", [x]) => {
                write!(f, "!")?;
                x.fmt_at(f, UNARY)
            }
            ("ite", [c, a, b]) => {
                write!(f, "if ")?;
                c.fmt_at(f, 0)?;
                write!(f, " {{ ")?;
                a.fmt_at(f, 0)?;
                write!(f, " }} else {{ ")?;
                b.fmt_at(f, 0)?;
                write!(f, " }}")
            }
            ("tuple", xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    let sep = if i > 0 { ", " } else { "" };
                    write!(f, "{sep}")?;
                    x.fmt_at(f, 0)?;
                }
                write!(f, "{})", if xs.len() == 1 { "," } else { "" })
            }
            (proj, [x]) if proj.starts_with('.') => {
                x.fmt_at(f, POSTFIX)?;
                write!(f, "{proj}")
            }
            ("seq.len", [x]) => {
                x.fmt_at(f, POSTFIX)?;
                write!(f, ".len()")
            }
            ("seq.nth" | "select", [x, i]) => {
                x.fmt_at(f, POSTFIX)?;
                write!(f, "[")?;
                i.fmt_at(f, 0)?;
                write!(f, "]")
            }
            (op, xs) if xs.len() >= 2 && infix(op).is_some() => {
                let (sym, prec) = infix(op).unwrap();
                // `==>` groups to the right, the comparisons not at all, the rest to the left.
                let (first, rest) = match prec {
                    IMPLIES => (prec + 1, prec),
                    CMP => (prec + 1, prec + 1),
                    _ => (prec, prec + 1),
                };
                xs[0].fmt_at(f, first)?;
                for x in &xs[1..] {
                    write!(f, " {sym} ")?;
                    x.fmt_at(f, rest)?;
                }
                Ok(())
            }
            (head, xs) => {
                write!(f, "{head}(")?;
                for (i, x) in xs.iter().enumerate() {
                    let sep = if i > 0 { ", " } else { "" };
                    write!(f, "{sep}")?;
                    x.fmt_at(f, 0)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_at(f, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(x: &str) -> Expr {
        Expr::sym(x)
    }

    fn a(f: &str, xs: Vec<Expr>) -> Expr {
        Expr::app(f, xs)
    }

    #[test]
    fn prints_annotation_syntax() {
        let e = a(
            "=>",
            vec![
                a("and", vec![a(">=", vec![s("n"), s("0")]), s("p")]),
                a("=", vec![s("result"), a("*", vec![s("2"), s("n")])]),
            ],
        );
        assert_eq!(e.to_string(), "n >= 0 && p ==> result == 2 * n");
    }

    #[test]
    fn parenthesizes_by_precedence() {
        let e = a("*", vec![a("+", vec![s("x"), s("1")]), s("y")]);
        assert_eq!(e.to_string(), "(x + 1) * y");
        let e = a("-", vec![s("x"), a("-", vec![s("y"), s("z")])]);
        assert_eq!(e.to_string(), "x - (y - z)");
        let e = a("not", vec![a("and", vec![s("a"), s("b")])]);
        assert_eq!(e.to_string(), "!(a && b)");
        let e = a("not", vec![a("=", vec![s("y"), s("6")])]);
        assert_eq!(e.to_string(), "y != 6");
        let e = a("or", vec![a("and", vec![s("a"), s("b")]), s("c")]);
        assert_eq!(e.to_string(), "a && b || c");
        let e = a("and", vec![a("or", vec![s("a"), s("b")]), s("c")]);
        assert_eq!(e.to_string(), "(a || b) && c");
    }

    #[test]
    fn prints_references_and_projections() {
        let e = a(
            "=",
            vec![
                a("final", vec![s("x")]),
                a("+", vec![a("deref", vec![s("x")]), s("1")]),
            ],
        );
        assert_eq!(e.to_string(), "!x == *x + 1");
        let e = a(".0", vec![a("deref", vec![s("p")])]);
        assert_eq!(e.to_string(), "(*p).0");
    }

    #[test]
    fn normalize_reads_through_mut_pairs() {
        let m = |c: &str, f: &str| a("Mut::new", vec![s(c), s(f)]);
        let e = a("=", vec![m("a", "b"), m("c", "d")]).normalize();
        assert_eq!(e.to_string(), "a == c && b == d");
        let e = a(
            "=",
            vec![a("final", vec![m("a", "b")]), a("deref", vec![m("a", "b")])],
        )
        .normalize();
        assert_eq!(e.to_string(), "b == a");
        let e = a("=", vec![a("<", vec![s("i"), s("n")]), s("false")]).normalize();
        assert_eq!(e.to_string(), "i >= n");
    }

    #[test]
    fn normalize_reads_linear_arithmetic() {
        let neg = |x: Expr| a("*", vec![a("-", vec![s("1")]), x]);
        let e = a(
            "not",
            vec![a(
                "<=",
                vec![
                    a("+", vec![a("*", vec![s("2"), s("i")]), neg(s("s"))]),
                    a("-", vec![s("1")]),
                ],
            )],
        );
        assert_eq!(e.normalize().to_string(), "2 * i - s > -1");
    }

    #[test]
    fn and_drops_true_and_flattens() {
        let e = Expr::and(vec![Expr::tt(), a("and", vec![s("a"), Expr::tt()]), s("b")]);
        assert_eq!(e.to_string(), "a && b");
        assert!(Expr::and(vec![Expr::tt()]).is_true());
    }
}
