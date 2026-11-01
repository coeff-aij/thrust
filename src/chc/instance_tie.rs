//! The SMT-LIB2 text of a generic unknown read at a concrete instance
//! (`THRUST_GENERIC_UNKNOWN_PREDS=1`).
//!
//! A generic unknown `G` is declared over a generic item's forall sorts with an empty dependency
//! set and takes each universal it may read as a curried array argument
//! ([`chc::System::generic_unknown_universals`]); the generic clauses pass the universal itself.
//! An instance `X` of it is an unknown of its own over the instance's sorts, tied to `G` by
//!
//! ```text
//! proj(ū, x̄) ∧ G(Λ̄, ū) ⇒ X(x̄)        X(x̄) ∧ proj(ū, x̄) ⇒ G(Λ̄, ū)
//! ```
//!
//! where each `Λ` is a `lambda` stating the instance's definition of a universal, and `proj`
//! reads a value of a forall sort as a value of the instance's sort through a universal
//! projection function, componentwise through tuples, `Box` and `Mut`. A projection relates
//! values only as a clause premise. The one law is a sequence projection's, that it maps the
//! elements; a law that made a projection invertible would force a cardinality on the forall
//! sort, which may be any non-empty set. At the interpretation that gives each forall sort the
//! instance's sort and each projection the identity, the laws hold and the clauses say
//! `X = G(Λ̄)`, so `X` is a relation the generic proofs hold of at the instance.

use std::collections::{BTreeMap, HashMap};

use super::format_context::FormatContext;
use super::sexp::{self, Sexp};
use crate::chc;

/// A definition that can be inlined into a `lambda`: its parameters' names and its body.
pub type Inline = (Vec<String>, Sexp);

/// The projections a set of ties needs, each a universal function from a sort with forall sorts
/// to the sort the instance gives it.
#[derive(Default)]
pub struct Projections {
    /// `(generic sort, instance sort)` to the function's name, in the order first needed.
    funs: BTreeMap<(chc::Sort, chc::Sort), String>,
    /// The `:law` of a function, by name: a sequence's projection maps its elements.
    laws: BTreeMap<String, String>,
    /// The element sort of each sequence projection, by name.
    seq_elems: BTreeMap<String, chc::Sort>,
    fresh: usize,
}

impl Projections {
    /// Every projection function as a `declare-forall-fun`.
    pub fn declarations(&self, ctx: &FormatContext) -> Vec<String> {
        let mut decls: Vec<_> = self
            .funs
            .iter()
            .map(|((generic, instance), name)| {
                let law = match self.laws.get(name) {
                    Some(law) => format!(" :law {law}"),
                    None => String::new(),
                };
                format!(
                    "(declare-forall-fun {name} ({}) {}{law})",
                    ctx.fmt_sort(generic),
                    ctx.fmt_sort(instance)
                )
            })
            .collect();
        decls.sort();
        decls
    }

    fn fun(&mut self, generic: &chc::Sort, instance: &chc::Sort) -> String {
        let next = self.funs.len();
        self.funs
            .entry((generic.clone(), instance.clone()))
            .or_insert_with(|| format!("thrust_proj_{next}"))
            .clone()
    }

    fn fresh_var(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}{}", self.fresh)
    }
}

/// One tie's text, built against the sort substitution of its instance.
pub struct TieText<'a> {
    ctx: &'a FormatContext,
    subst: HashMap<chc::ForallSortIdx, chc::Sort>,
    projections: &'a mut Projections,
}

impl<'a> TieText<'a> {
    pub fn new(
        ctx: &'a FormatContext,
        generic_sig: &[chc::Sort],
        instance_sig: &[chc::Sort],
        projections: &'a mut Projections,
    ) -> Self {
        let mut subst = HashMap::new();
        for (generic, instance) in generic_sig.iter().zip(instance_sig) {
            unify(generic, instance, &mut subst);
        }
        Self {
            ctx,
            subst,
            projections,
        }
    }

    fn instance_sort(&self, generic: &chc::Sort) -> chc::Sort {
        generic.subst_forall(&|idx| self.subst.get(&idx).cloned())
    }

    /// `t`, of sort `generic`, read as a value of the instance's sort.
    fn project(&mut self, generic: &chc::Sort, t: &str) -> String {
        let instance = self.instance_sort(generic);
        if instance == *generic {
            return t.to_string();
        }
        match generic {
            chc::Sort::Tuple(gs) => {
                let is: Vec<_> = gs.iter().map(|g| self.instance_sort(g)).collect();
                let elems: Vec<_> = gs
                    .iter()
                    .enumerate()
                    .map(|(i, g)| {
                        let proj = format!("({} {t})", self.ctx.tuple_proj(gs, i));
                        self.project(g, &proj)
                    })
                    .collect();
                format!("({} {})", self.ctx.tuple_ctor(&is), elems.join(" "))
            }
            chc::Sort::Box(g) => {
                let inner = format!("({} {t})", self.ctx.box_current(g));
                let inner = self.project(g, &inner);
                format!("({} {inner})", self.ctx.box_ctor(&self.instance_sort(g)))
            }
            chc::Sort::Mut(g) => {
                let current = format!("({} {t})", self.ctx.mut_current(g));
                let final_ = format!("({} {t})", self.ctx.mut_final(g));
                let current = self.project(g, &current);
                let final_ = self.project(g, &final_);
                format!(
                    "({} {current} {final_})",
                    self.ctx.mut_ctor(&self.instance_sort(g))
                )
            }
            chc::Sort::Seq(elem) => {
                let name = self.projections.fun(generic, &instance);
                if !self.projections.laws.contains_key(&name) {
                    let law = self.seq_law(&name, generic, elem);
                    self.projections.laws.insert(name.clone(), law);
                    self.projections
                        .seq_elems
                        .insert(name.clone(), (**elem).clone());
                }
                format!("({name} {t})")
            }
            _ => format!("({} {t})", self.projections.fun(generic, &instance)),
        }
    }

    /// The law of `name`, the projection of the sequence sort `generic` with elements `elem`: it
    /// keeps the length and projects each element. It holds of the identity when the forall
    /// sorts are the instance's, so it restricts the projections to a class that contains the
    /// interpretation the soundness argument uses, and forces no cardinality.
    fn seq_law(&mut self, name: &str, generic: &chc::Sort, elem: &chc::Sort) -> String {
        let t = self.projections.fresh_var("thrust_s");
        let k = self.projections.fresh_var("thrust_k");
        let elem_t = self.project(elem, &format!("(seq.nth {t} {k})"));
        format!(
            "(forall (({t} {})) (and (= (seq.len ({name} {t})) (seq.len {t})) (forall (({k} Int)) (=> (and (<= 0 {k}) (< {k} (seq.len {t}))) (= (seq.nth ({name} {t}) {k}) {elem_t})))))",
            self.ctx.fmt_sort(generic)
        )
    }

    /// The premises that `u`, of sort `generic`, reads as `x`. A sequence is related element by
    /// element, its projection's law at `u`: PCSat does not insert the law for a projection
    /// applied on its own, and an equation through the projection function slows its refutations
    /// (no answer at 60 s on `take`'s fail twin, against 1.2 s without it). A tuple, `Box` or
    /// `Mut` that holds such a sequence is related component by component; any other value by
    /// one equation, since relating `take`'s `(a2, Int)` component by component also left its
    /// fail twin without an answer at 60 s.
    fn premises(&mut self, generic: &chc::Sort, u: &str, x: &str) -> Vec<String> {
        let instance = self.instance_sort(generic);
        if instance == *generic {
            return vec![format!("(= {u} {x})")];
        }
        if !self.holds_projected_seq(generic) {
            return vec![format!("(= {} {x})", self.project(generic, u))];
        }
        match generic {
            chc::Sort::Tuple(gs) => {
                let is: Vec<_> = gs.iter().map(|g| self.instance_sort(g)).collect();
                let mut premises = Vec::new();
                for (i, g) in gs.iter().enumerate() {
                    let u_i = format!("({} {u})", self.ctx.tuple_proj(gs, i));
                    let x_i = format!("({} {x})", self.ctx.tuple_proj(&is, i));
                    premises.extend(self.premises(g, &u_i, &x_i));
                }
                premises
            }
            chc::Sort::Box(g) => {
                let u_c = format!("({} {u})", self.ctx.box_current(g));
                let x_c = format!("({} {x})", self.ctx.box_current(&self.instance_sort(g)));
                self.premises(g, &u_c, &x_c)
            }
            chc::Sort::Mut(g) => {
                let i = self.instance_sort(g);
                let (u_c, x_c) = (
                    format!("({} {u})", self.ctx.mut_current(g)),
                    format!("({} {x})", self.ctx.mut_current(&i)),
                );
                let (u_f, x_f) = (
                    format!("({} {u})", self.ctx.mut_final(g)),
                    format!("({} {x})", self.ctx.mut_final(&i)),
                );
                let mut premises = self.premises(g, &u_c, &x_c);
                premises.extend(self.premises(g, &u_f, &x_f));
                premises
            }
            chc::Sort::Seq(elem) => {
                let k = self.projections.fresh_var("thrust_k");
                let elem_u = self.project(elem, &format!("(seq.nth {u} {k})"));
                vec![
                    format!("(= (seq.len {u}) (seq.len {x}))"),
                    format!(
                        "(forall (({k} Int)) (=> (and (<= 0 {k}) (< {k} (seq.len {x}))) (= {elem_u} (seq.nth {x} {k}))))"
                    ),
                ]
            }
            _ => vec![format!("(= {} {x})", self.project(generic, u))],
        }
    }

    /// Whether `generic` holds, through tuples, `Box` and `Mut`, a sequence whose projection is
    /// not the identity.
    fn holds_projected_seq(&self, generic: &chc::Sort) -> bool {
        if self.instance_sort(generic) == *generic {
            return false;
        }
        match generic {
            chc::Sort::Seq(_) => true,
            chc::Sort::Tuple(gs) => gs.iter().any(|g| self.holds_projected_seq(g)),
            chc::Sort::Box(g) | chc::Sort::Mut(g) => self.holds_projected_seq(g),
            _ => false,
        }
    }

    /// The `lambda` stating `definition` as the value of the universal `pred`, curried over its
    /// parameters. A definition given as `inline` has its body substituted rather than called,
    /// with a projected sequence read element by element, so that the solver sees each element's
    /// projection where the body reads it.
    fn lambda(
        &mut self,
        pred: &chc::ForallPred,
        definition: &str,
        inline: Option<Inline>,
    ) -> String {
        let params: Vec<_> = pred
            .params()
            .iter()
            .map(|sort| (self.projections.fresh_var("thrust_l"), sort.clone()))
            .collect();
        let args: Vec<_> = params
            .iter()
            .map(|(name, sort)| self.project(sort, name))
            .collect();
        let mut text = match inline {
            Some((names, body)) if names.len() == args.len() => {
                let args: HashMap<_, _> = names
                    .into_iter()
                    .zip(args.iter().map(|a| parse_one(a)))
                    .collect();
                self.read_elementwise(substitute(body, &args)).to_string()
            }
            _ => format!("({definition} {})", args.join(" ")),
        };
        for (name, sort) in params.iter().rev() {
            text = format!("(lambda (({name} {})) {text})", self.ctx.fmt_sort(sort));
        }
        text
    }

    /// `body` with `(seq.nth (P s) k)` read as the element projection of `(seq.nth s k)` and
    /// `(seq.len (P s))` as `(seq.len s)`, for each sequence projection `P`.
    fn read_elementwise(&mut self, body: Sexp) -> Sexp {
        let Sexp::List(items) = body else {
            return body;
        };
        let items: Vec<_> = items
            .into_iter()
            .map(|item| self.read_elementwise(item))
            .collect();
        let projected = |item: &Sexp| -> Option<(chc::Sort, Sexp)> {
            let Sexp::List(app) = item else { return None };
            let [Sexp::Atom(f), s] = app.as_slice() else {
                return None;
            };
            let elem = self.projections.seq_elems.get(f)?;
            Some((elem.clone(), s.clone()))
        };
        match items.as_slice() {
            [Sexp::Atom(op), seq, k] if op == "seq.nth" => {
                if let Some((elem, s)) = projected(seq) {
                    let read = format!("(seq.nth {s} {k})");
                    return parse_one(&self.project(&elem, &read));
                }
            }
            [Sexp::Atom(op), seq] if op == "seq.len" => {
                if let Some((_, s)) = projected(seq) {
                    return Sexp::List(vec![Sexp::Atom("seq.len".to_string()), s]);
                }
            }
            _ => {}
        }
        Sexp::List(items)
    }

    /// The two clauses of the tie; `inline` gives the definitions that can be inlined.
    pub fn clauses(
        &mut self,
        tie: &chc::InstanceTie,
        generic_sig: &[chc::Sort],
        instance_sig: &[chc::Sort],
        inline: &dyn Fn(&str) -> Option<Inline>,
    ) -> [String; 2] {
        let mut binders = Vec::new();
        let mut premises = Vec::new();
        let mut us = Vec::new();
        let mut xs = Vec::new();
        for (i, (generic, instance)) in generic_sig.iter().zip(instance_sig).enumerate() {
            let (u, x) = (format!("thrust_u{i}"), format!("thrust_x{i}"));
            binders.push(format!("({u} {})", self.ctx.fmt_sort(generic)));
            binders.push(format!("({x} {})", self.ctx.fmt_sort(instance)));
            premises.extend(self.premises(generic, &u, &x));
            us.push(u);
            xs.push(x);
        }
        let lambdas: Vec<_> = tie
            .definitions
            .iter()
            .map(|(pred, definition)| self.lambda(pred, definition, inline(definition)))
            .collect();
        let generic = format!("({} {} {})", tie.generic, lambdas.join(" "), us.join(" "));
        let instance = format!("({} {})", tie.instance, xs.join(" "));
        let binders = binders.join(" ");
        let premises = premises.join(" ");
        [
            format!("(assert (forall ({binders}) (=> (and {premises} {generic}) {instance})))"),
            format!("(assert (forall ({binders}) (=> (and {instance} {premises}) {generic})))"),
        ]
    }
}

/// The curried array sort of a universal passed as an argument: PCSat reads a forall predicate
/// of arity n as `(Array s1 (Array s2 ... (Array sn Bool)))` and has no multi-index arrays.
pub fn curried_array_sort(ctx: &FormatContext, pred: &chc::ForallPred) -> String {
    let mut text = "Bool".to_string();
    for sort in pred.params().iter().rev() {
        text = format!("(Array {} {text})", ctx.fmt_sort(sort));
    }
    text
}

/// Records in `subst` the sort each forall sort of `generic` stands at in `instance`.
fn unify(
    generic: &chc::Sort,
    instance: &chc::Sort,
    subst: &mut HashMap<chc::ForallSortIdx, chc::Sort>,
) {
    match (generic, instance) {
        (chc::Sort::Forall(idx), _) => {
            subst.insert(*idx, instance.clone());
        }
        (chc::Sort::Box(g), chc::Sort::Box(i))
        | (chc::Sort::Mut(g), chc::Sort::Mut(i))
        | (chc::Sort::Seq(g), chc::Sort::Seq(i)) => unify(g, i, subst),
        (chc::Sort::Tuple(gs), chc::Sort::Tuple(is)) if gs.len() == is.len() => {
            for (g, i) in gs.iter().zip(is) {
                unify(g, i, subst);
            }
        }
        (chc::Sort::Array(g1, g2), chc::Sort::Array(i1, i2)) => {
            unify(g1, i1, subst);
            unify(g2, i2, subst);
        }
        (chc::Sort::Datatype(g), chc::Sort::Datatype(i)) if g.symbol == i.symbol => {
            for (g, i) in g.args.iter().zip(&i.args) {
                unify(g, i, subst);
            }
        }
        _ => {}
    }
}

fn parse_one(text: &str) -> Sexp {
    sexp::parse_all(text)
        .into_iter()
        .next()
        .expect("a projection is one term")
}

/// `body` with each atom `args` names replaced. The bodies inlined bind their own variables only
/// as `q$<n>` or `v<n>` of a nested definition's text, never the parameter names `args` holds
/// at the top level, except through a binder of the same name, which this keeps.
fn substitute(body: Sexp, args: &HashMap<String, Sexp>) -> Sexp {
    match body {
        Sexp::Atom(a) => args.get(&a).cloned().unwrap_or(Sexp::Atom(a)),
        Sexp::List(items) => {
            let binds = |s: &Sexp| matches!(s, Sexp::Atom(a) if ["forall", "exists", "lambda", "let"].contains(&a.as_str()));
            if items.first().is_some_and(binds) {
                let bound: Vec<String> = match items.get(1) {
                    Some(Sexp::List(bs)) => bs
                        .iter()
                        .filter_map(|b| match b {
                            Sexp::List(b) => b.first().and_then(Sexp::atom).map(str::to_string),
                            _ => None,
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                let inner: HashMap<_, _> = args
                    .iter()
                    .filter(|(k, _)| !bound.contains(k))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
                return Sexp::List(items.into_iter().map(|i| substitute(i, &inner)).collect());
            }
            Sexp::List(items.into_iter().map(|i| substitute(i, args)).collect())
        }
    }
}
