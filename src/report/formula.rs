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
        let pred = chc::UserDefinedPred::new(info.name.clone()).into();
        let args = names.arrange(p, &atom.args);
        Formula::Atom(chc::Atom {
            guard: atom.guard,
            pred,
            args,
        })
    });
    let mut f = tidy(f);
    f.simplify();
    f.one_line()
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

/// The components of two pairs or tuples equated.
fn componentwise<V>(xs: Vec<chc::Term<V>>, ys: Vec<chc::Term<V>>) -> chc::Formula<V> {
    let eq = |(x, y)| tidy_atom(chc::Atom::new(chc::KnownPred::EQUAL.into(), vec![x, y]));
    chc::Formula::And(xs.into_iter().zip(ys).map(eq).collect())
}

/// `atom` with its arguments tidied (see `tidy_term`), two pairs `<c, f>` or two tuples equal
/// when their components are, and a comparison equated with `true` or `false` read as the comparison or its
/// negation.
fn tidy_atom<V>(atom: chc::Atom<V>) -> chc::Formula<V> {
    use chc::{KnownPred, Term};
    let args: Vec<Term<V>> = atom.args.into_iter().map(tidy_term).collect();
    let equal = matches!(atom.pred, chc::Pred::Known(p) if p == KnownPred::EQUAL);
    let not_equal = matches!(atom.pred, chc::Pred::Known(p) if p == KnownPred::NOT_EQUAL);
    if atom.guard.is_some() || !(equal || not_equal) || args.len() != 2 {
        return chc::Atom { args, ..atom }.into();
    }
    let [a, b] = <[Term<V>; 2]>::try_from(args).ok().unwrap();
    match (a, b) {
        (Term::Mut(c1, f1), Term::Mut(c2, f2)) if equal => {
            componentwise(vec![*c1, *f1], vec![*c2, *f2])
        }
        (Term::Tuple(xs), Term::Tuple(ys)) if equal && xs.len() == ys.len() => {
            componentwise(xs, ys)
        }
        (Term::App(op, xs), Term::Bool(b)) | (Term::Bool(b), Term::App(op, xs))
            if xs.len() == 2 && chc::KnownPred::named(op.name()).is_some() =>
        {
            let p = chc::KnownPred::named(op.name()).unwrap();
            let p = if b == equal { p } else { negated(p).unwrap() };
            chc::Atom::new(p.into(), xs).into()
        }
        (a, b) => chc::Atom::new(atom.pred, vec![a, b]).into(),
    }
}

/// `f` with what reads as noise rewritten into an equivalent formula: see `tidy_atom`, and a
/// negated comparison is the opposite comparison.
pub fn tidy<V>(f: chc::Formula<V>) -> chc::Formula<V> {
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
        Formula::And(fs) => Formula::And(all(fs)),
        Formula::Or(fs) => Formula::Or(all(fs)),
        Formula::Implies(a, b) => Formula::Implies(Box::new(tidy(*a)), Box::new(tidy(*b))),
        Formula::Exists(vars, f) => Formula::Exists(vars, Box::new(tidy(*f))),
        Formula::Forall(vars, f) => Formula::Forall(vars, Box::new(tidy(*f))),
    }
}
