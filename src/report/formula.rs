//! Formulas as the report shows them: Thrust's own [`chc::Formula`]s over variables named as the
//! program names them, printed by Thrust's printer. The solver's answers are read into the same
//! formulas (see [`super::model`]).

use std::collections::BTreeSet;
use std::sync::Mutex;

use crate::chc;

use super::sites::Names;

/// A variable, by the name the report shows it with.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(&'static str);

impl Name {
    /// The variable named `name`. A report is made once in a run, so the names live to its end.
    pub fn new(name: &str) -> Name {
        static NAMES: Mutex<BTreeSet<&'static str>> = Mutex::new(BTreeSet::new());
        let mut names = NAMES.lock().unwrap();
        if let Some(known) = names.get(name) {
            return Name(known);
        }
        let leaked: &'static str = Box::leak(name.to_owned().into_boxed_str());
        names.insert(leaked);
        Name(leaked)
    }
}

impl Name {
    pub fn as_str(&self) -> &'static str {
        self.0
    }
}

impl std::fmt::Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}

pub type Term = chc::Term<Name>;
pub type Atom = chc::Atom<Name>;
pub type Formula = chc::Formula<Name>;

/// What Thrust's printer writes, on one line.
pub trait OneLine {
    fn one_line(&self) -> String;
}

macro_rules! one_line {
    ($($t:ty),*) => {$(
        impl OneLine for $t {
            fn one_line(&self) -> String {
                // One group around the whole lays every line inside it flat.
                let arena = pretty::Arena::new();
                let doc = pretty::Pretty::pretty(self, &arena).group();
                let mut out = String::new();
                doc.1.render_fmt(1 << 20, &mut out).unwrap();
                out
            }
        }
    )*};
}

one_line!(Formula, Term, chc::Sort);

/// `f` with each atom replaced by `g` of it.
pub fn map_atoms(f: Formula, g: &impl Fn(Atom) -> Formula) -> Formula {
    let all = |fs: Vec<Formula>| fs.into_iter().map(|f| map_atoms(f, g)).collect();
    match f {
        Formula::Atom(atom) => g(atom),
        Formula::Not(f) => Formula::Not(Box::new(map_atoms(*f, g))),
        Formula::And(fs) => Formula::And(all(fs)),
        Formula::Or(fs) => Formula::Or(all(fs)),
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(map_atoms(*a, g)), Box::new(map_atoms(*b, g)))
        }
        Formula::Exists(vars, f) => Formula::Exists(vars, Box::new(map_atoms(*f, g))),
        Formula::Forall(vars, f) => Formula::Forall(vars, Box::new(map_atoms(*f, g))),
    }
}

/// `f` as the report shows it: each predicate variable the report names by its name, with its
/// arguments in the order they are shown in (see [`Names::arrange`]).
pub fn show(f: &Formula, names: &Names) -> String {
    let f = map_atoms(f.clone(), &|atom| {
        let chc::Pred::Var(p) = atom.pred else {
            return Formula::Atom(atom);
        };
        let Some(info) = names.preds.get(&p) else {
            return Formula::Atom(atom);
        };
        let args = names.arrange(p, &atom.args);
        let applied = applied(&info.name, &info.args, args);
        Formula::Atom(chc::Atom {
            guard: atom.guard,
            pred: chc::UserDefinedPred::new(applied).into(),
            args: Vec::new(),
        })
    });
    let mut f = tidy(f);
    f.simplify();
    f.one_line()
}

/// `p(…)` with each argument as the run shows a fact's: `name = term` for the variable of the
/// template it is, a `&mut` as its current and final values `*name` and `°name`, and the name
/// alone where the term is that variable.
fn applied(pred: &str, params: &[Option<String>], args: Vec<Term>) -> String {
    if args.is_empty() {
        return pred.to_owned();
    }
    let mut shown = Vec::new();
    for (param, arg) in params
        .iter()
        .map(Option::as_deref)
        .chain(std::iter::repeat(None))
        .zip(args)
    {
        push_argument(&mut shown, param, tidy_term(arg));
    }
    format!("{pred}({})", shown.join(", "))
}

fn push_argument(shown: &mut Vec<String>, param: Option<&str>, arg: Term) {
    let Some(name) = param else {
        shown.push(arg.one_line());
        return;
    };
    if let Term::Mut(current, last) = arg {
        push_argument(shown, Some(&format!("*{name}")), *current);
        push_argument(shown, Some(&format!("°{name}")), *last);
        return;
    }
    match arg {
        Term::Var(v) if v.as_str() == name => shown.push(name.to_owned()),
        arg => shown.push(format!("{name} = {}", arg.one_line())),
    }
}

pub fn and(fs: Vec<Formula>) -> Formula {
    let mut f = Formula::And(fs);
    f.simplify();
    f
}

/// The comparison `p` negated, if `p` is one.
fn negated(p: chc::KnownPred) -> Option<chc::KnownPred> {
    use chc::KnownPred;
    let pairs = [
        (KnownPred::EQUAL, KnownPred::NOT_EQUAL),
        (KnownPred::LESS_THAN_OR_EQUAL, KnownPred::GREATER_THAN),
        (KnownPred::GREATER_THAN_OR_EQUAL, KnownPred::LESS_THAN),
    ];
    pairs.into_iter().find_map(|(a, b)| match p {
        _ if p == a => Some(b),
        _ if p == b => Some(a),
        _ => None,
    })
}

/// `t` with the current and final values of a pair `<c, f>` read as `c` and `f`, a component of a
/// tuple written out as that component, `-1 * x` as
/// `-x` and `a + -b` as `a - b`.
fn tidy_term<V>(t: chc::Term<V>) -> chc::Term<V> {
    use chc::{Function, Term};
    let tidy = |t: Box<Term<V>>| Box::new(tidy_term(*t));
    match t {
        Term::MutCurrent(m) => match tidy_term(*m) {
            Term::Mut(c, _) => *c,
            m => Term::MutCurrent(Box::new(m)),
        },
        Term::MutFinal(m) => match tidy_term(*m) {
            Term::Mut(_, f) => *f,
            m => Term::MutFinal(Box::new(m)),
        },
        Term::Mut(c, f) => Term::Mut(tidy(c), tidy(f)),
        Term::App(f, args) => {
            let args: Vec<Term<V>> = args.into_iter().map(tidy_term).collect();
            match <[Term<V>; 2]>::try_from(args) {
                Ok([Term::Int(m), x]) if f == Function::MUL && m == (-1).into() => {
                    Term::App(Function::NEG, vec![x])
                }
                Ok([a, Term::App(g, mut b)]) if f == Function::ADD && g == Function::NEG => {
                    Term::App(Function::SUB, vec![a, b.remove(0)])
                }
                Ok([Term::App(g, mut b), a]) if f == Function::ADD && g == Function::NEG => {
                    Term::App(Function::SUB, vec![a, b.remove(0)])
                }
                Ok(args) => Term::App(f, args.into()),
                Err(args) => Term::App(f, args),
            }
        }
        Term::Tuple(ts) => Term::Tuple(ts.into_iter().map(tidy_term).collect()),
        Term::TupleProj(t, i) => match tidy_term(*t) {
            Term::Tuple(mut ts) if i < ts.len() => ts.swap_remove(i),
            t => Term::TupleProj(Box::new(t), i),
        },
        t => t,
    }
}

/// The formula a boolean term `t` stands for, if it is a comparison or a connective of them.
fn as_formula<V>(t: chc::Term<V>) -> Option<chc::Formula<V>> {
    use chc::{Formula, Function, Term};
    let all = |ts: Vec<Term<V>>| ts.into_iter().map(as_formula).collect::<Option<Vec<_>>>();
    match t {
        Term::Bool(true) => Some(Formula::top()),
        Term::Bool(false) => Some(Formula::bottom()),
        Term::App(f, mut ts) if f == Function::NOT && ts.len() == 1 => {
            Some(as_formula(ts.remove(0))?.not())
        }
        Term::App(f, ts) if f == Function::AND => Some(Formula::And(all(ts)?)),
        Term::App(f, ts) if f == Function::OR => Some(Formula::Or(all(ts)?)),
        Term::App(f, ts) if ts.len() == 2 => {
            let p = chc::KnownPred::named(f.name())?;
            Some(chc::Atom::new(p.into(), ts).into())
        }
        _ => None,
    }
}

/// `x - y` as `(x, y)`.
fn difference<V: Clone>(t: &chc::Term<V>) -> Option<(chc::Term<V>, chc::Term<V>)> {
    match t {
        chc::Term::App(f, ts) if *f == chc::Function::SUB && ts.len() == 2 => {
            Some((ts[0].clone(), ts[1].clone()))
        }
        _ => None,
    }
}

/// `x - y` compared by `p` with the integer `k`, as `x` compared with `y` moved by `k`: over the
/// integers a strict bound is the bound by the neighbour, so `x - y <= -1` is `x < y` and
/// `x - y > -1` is `x >= y`.
fn compared_difference<V>(
    p: chc::KnownPred,
    x: chc::Term<V>,
    y: chc::Term<V>,
    k: num_bigint::BigInt,
) -> chc::Atom<V> {
    use chc::{KnownPred, Term};
    let (p, k) = match p {
        p if p == KnownPred::LESS_THAN => (KnownPred::LESS_THAN_OR_EQUAL, k - 1),
        p if p == KnownPred::GREATER_THAN => (KnownPred::GREATER_THAN_OR_EQUAL, k + 1),
        p => (p, k),
    };
    let one: num_bigint::BigInt = 1.into();
    let (p, k) = match p {
        p if p == KnownPred::LESS_THAN_OR_EQUAL && k == -one.clone() => {
            (KnownPred::LESS_THAN, 0.into())
        }
        p if p == KnownPred::GREATER_THAN_OR_EQUAL && k == one => {
            (KnownPred::GREATER_THAN, 0.into())
        }
        p => (p, k),
    };
    let y = match k {
        k if k == 0.into() => y,
        k if k > 0.into() => Term::App(chc::Function::ADD, vec![y, Term::Int(k)]),
        k => Term::App(chc::Function::SUB, vec![y, Term::Int(-k)]),
    };
    chc::Atom::new(p.into(), vec![x, y])
}

/// The components of two pairs or tuples equated.
fn componentwise<V: Clone + PartialEq>(
    xs: Vec<chc::Term<V>>,
    ys: Vec<chc::Term<V>>,
) -> chc::Formula<V> {
    let eq = |(x, y)| tidy_atom(chc::Atom::new(chc::KnownPred::EQUAL.into(), vec![x, y]));
    chc::Formula::And(xs.into_iter().zip(ys).map(eq).collect())
}

/// `atom` with its arguments tidied (see `tidy_term`), two pairs `<c, f>` or two tuples equal
/// when their components are, a boolean term equated with `true` or `false` read as the formula
/// it stands for or its negation, and `x - y` compared with `0` as `x` compared with `y`.
fn tidy_atom<V: Clone + PartialEq>(atom: chc::Atom<V>) -> chc::Formula<V> {
    use chc::{KnownPred, Term};
    let args: Vec<Term<V>> = atom.args.into_iter().map(tidy_term).collect();
    let comparison = match atom.pred {
        chc::Pred::Known(p) => KnownPred::named(p.name()) == Some(p) || p == KnownPred::NOT_EQUAL,
        _ => false,
    };
    if atom.guard.is_some() || !comparison || args.len() != 2 {
        return chc::Atom { args, ..atom }.into();
    }
    let [a, b] = <[Term<V>; 2]>::try_from(args).ok().unwrap();
    let chc::Pred::Known(p) = atom.pred else {
        unreachable!()
    };
    if let (Some((x, y)), Term::Int(k)) = (difference(&a), &b) {
        return compared_difference(p, x, y, k.clone()).into();
    }
    let equal = matches!(atom.pred, chc::Pred::Known(p) if p == KnownPred::EQUAL);
    let not_equal = matches!(atom.pred, chc::Pred::Known(p) if p == KnownPred::NOT_EQUAL);
    if !(equal || not_equal) {
        return chc::Atom::new(atom.pred, vec![a, b]).into();
    }
    let read = match (&a, &b) {
        (Term::Bool(value), t) | (t, Term::Bool(value)) if !matches!(t, Term::Bool(_)) => {
            as_formula(t.clone()).map(|f| if *value == equal { f } else { f.not() })
        }
        _ => None,
    };
    if let Some(f) = read {
        return tidy(f);
    }
    match (a, b) {
        (Term::Mut(c1, f1), Term::Mut(c2, f2)) if equal => {
            componentwise(vec![*c1, *f1], vec![*c2, *f2])
        }
        (Term::Tuple(xs), Term::Tuple(ys)) if equal && xs.len() == ys.len() => {
            componentwise(xs, ys)
        }
        (a, b) => chc::Atom::new(atom.pred, vec![a, b]).into(),
    }
}

/// `f` with what reads as noise rewritten into an equivalent formula: see `tidy_atom`, and a
/// negated comparison is the opposite comparison.
pub fn tidy<V: Clone + PartialEq>(f: chc::Formula<V>) -> chc::Formula<V> {
    use chc::Formula;
    let all = |fs: Vec<Formula<V>>| fs.into_iter().map(tidy).collect();
    match f {
        Formula::Atom(atom) => tidy_atom(atom),
        Formula::Not(f) => match tidy(*f) {
            Formula::Atom(chc::Atom {
                guard: None,
                pred: chc::Pred::Known(p),
                args,
            }) if negated(p).is_some() => chc::Atom::new(negated(p).unwrap().into(), args).into(),
            f => f.not(),
        },
        Formula::And(fs) => Formula::And(equalities(all(fs))),
        Formula::Or(fs) => Formula::Or(all(fs)),
        Formula::Implies(a, b) => Formula::Implies(Box::new(tidy(*a)), Box::new(tidy(*b))),
        Formula::Exists(vars, f) => Formula::Exists(vars, Box::new(tidy(*f))),
        Formula::Forall(vars, f) => Formula::Forall(vars, Box::new(tidy(*f))),
    }
}

/// The bound `f` puts on `x` by `y`, if it is one: `(x, y, true)` for `x <= y`, `(x, y, false)`
/// for `x >= y`; a strict bound by an integer is read as the bound by its neighbour.
fn bound<V: Clone>(f: &chc::Formula<V>) -> Option<(chc::Term<V>, chc::Term<V>, bool)> {
    use chc::{KnownPred, Term};
    let chc::Formula::Atom(chc::Atom {
        guard: None,
        pred: chc::Pred::Known(p),
        args,
    }) = f
    else {
        return None;
    };
    let [x, y] = <&[Term<V>; 2]>::try_from(args.as_slice()).ok()?;
    let step = |k: &num_bigint::BigInt, d: i32| Term::Int(k + d);
    let (y, upper) = match (*p, y) {
        (p, y) if p == KnownPred::LESS_THAN_OR_EQUAL => (y.clone(), true),
        (p, y) if p == KnownPred::GREATER_THAN_OR_EQUAL => (y.clone(), false),
        (p, Term::Int(k)) if p == KnownPred::LESS_THAN => (step(k, -1), true),
        (p, Term::Int(k)) if p == KnownPred::GREATER_THAN => (step(k, 1), false),
        _ => return None,
    };
    Some((x.clone(), y, upper))
}

/// `fs` with each two of them that bound a term from below and above by one value read as one
/// equation: `x <= y ∧ y <= x` and `t > -1 ∧ t < 1` as `x = y` and `t = 0`.
pub fn equalities<V: Clone + PartialEq>(mut fs: Vec<chc::Formula<V>>) -> Vec<chc::Formula<V>> {
    let mut i = 0;
    while i < fs.len() {
        let partner = bound(&fs[i]).and_then(|(x, y, upper)| {
            (i + 1..fs.len()).find_map(|j| {
                let (x2, y2, upper2) = bound(&fs[j])?;
                let opposite = x == x2 && y == y2 && upper != upper2;
                let flipped = x == y2 && y == x2 && upper == upper2;
                (opposite || flipped).then(|| (j, x.clone(), y.clone()))
            })
        });
        match partner {
            Some((j, x, y)) => {
                fs.remove(j);
                fs[i] = tidy_atom(chc::Atom::new(chc::KnownPred::EQUAL.into(), vec![x, y]));
            }
            None => i += 1,
        }
    }
    fs
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var(name: &str) -> Term {
        Term::var(Name::new(name))
    }

    fn atom(p: chc::KnownPred, a: Term, b: Term) -> Formula {
        chc::Atom::new(p.into(), vec![a, b]).into()
    }

    #[test]
    fn a_comparison_term_equated_with_a_truth_value_is_the_comparison() {
        let ne = var("a").ne(var("b"));
        let f = atom(chc::KnownPred::NOT_EQUAL, ne, Term::Bool(false));
        assert_eq!(tidy(f).one_line(), "a != b");
    }

    #[test]
    fn two_bounds_by_one_value_are_an_equation() {
        use chc::KnownPred;
        let d = var("s").sub(var("i").mul(Term::int(2)));
        let f = Formula::And(vec![
            atom(KnownPred::GREATER_THAN, d.clone(), Term::int(-1)),
            atom(KnownPred::LESS_THAN, d, Term::int(1)),
        ]);
        assert_eq!(tidy(f).one_line(), "s = i * 2");
        let g = Formula::And(vec![
            atom(
                KnownPred::LESS_THAN_OR_EQUAL,
                var("a").sub(var("r")),
                Term::int(0),
            ),
            atom(
                KnownPred::LESS_THAN_OR_EQUAL,
                var("r").sub(var("a")),
                Term::int(0),
            ),
        ]);
        assert_eq!(tidy(g).one_line(), "a = r");
    }

    #[test]
    fn a_difference_compared_with_an_integer_is_a_comparison() {
        use chc::KnownPred;
        let less = atom(
            KnownPred::LESS_THAN_OR_EQUAL,
            var("a").sub(var("r")),
            Term::int(-1),
        );
        assert_eq!(tidy(less).one_line(), "a < r");
        let at_least = atom(
            KnownPred::GREATER_THAN,
            var("n").sub(var("c")),
            Term::int(-1),
        );
        assert_eq!(tidy(at_least).one_line(), "n >= c");
        let moved = atom(
            KnownPred::LESS_THAN_OR_EQUAL,
            var("x").sub(var("y")),
            Term::int(2),
        );
        assert_eq!(tidy(moved).one_line(), "x <= y + 2");
    }

    #[test]
    fn bounds_that_do_not_meet_stay_bounds() {
        use chc::KnownPred;
        let strict = Formula::And(vec![
            atom(KnownPred::LESS_THAN, var("x"), var("y")),
            atom(KnownPred::GREATER_THAN, var("x"), var("y")),
        ]);
        assert_eq!(tidy(strict).one_line(), "x < y ∧ x > y");
        let same = Formula::And(vec![
            atom(KnownPred::LESS_THAN_OR_EQUAL, var("x"), Term::int(1)),
            atom(KnownPred::LESS_THAN_OR_EQUAL, var("x"), Term::int(1)),
        ]);
        assert_eq!(tidy(same).one_line(), "x <= 1 ∧ x <= 1");
    }
}
