//! Wrappers around CHC structures to display them in SMT-LIB2 format.
//!
//! The main entry point is the [`System`] wrapper, which takes a [`chc::System`] and provides a
//! [`std::fmt::Display`] implementation that produces a complete SMT-LIB2.
//! It uses [`FormatContext`] to handle the complexities of the conversion,
//! such as naming convention and solver-specific workarounds.
//! The output of this module is what gets passed to the external CHC solver.

use std::collections::HashMap;

use crate::chc::{self, format_context::FormatContext};

/// A helper struct to display a list of items.
#[derive(Debug, Clone)]
struct List<T> {
    open: Option<&'static str>,
    close: Option<&'static str>,
    delimiter: &'static str,
    items: Vec<T>,
}

impl<T> std::fmt::Display for List<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(c) = self.open {
            write!(f, "{}", c)?;
        }
        for (i, e) in self.items.iter().enumerate() {
            if i != 0 {
                write!(f, "{}", self.delimiter)?;
            }
            write!(f, "{}", e)?;
        }
        if let Some(c) = self.close {
            write!(f, "{}", c)?;
        }
        Ok(())
    }
}

impl<T> List<T> {
    pub fn closed<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: Some("("),
            close: Some(")"),
            delimiter: " ",
            items: inner.into_iter().collect(),
        }
    }

    pub fn multiline_closed<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: Some("(\n"),
            close: Some("\n)"),
            delimiter: "\n",
            items: inner.into_iter().collect(),
        }
    }

    pub fn multiline_open<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: None,
            close: None,
            delimiter: "\n",
            items: inner.into_iter().collect(),
        }
    }

    pub fn open<I>(inner: I) -> Self
    where
        I: std::iter::IntoIterator<Item = T>,
    {
        Self {
            open: None,
            close: None,
            delimiter: " ",
            items: inner.into_iter().collect(),
        }
    }
}

/// A wrapper around a [`chc::Term`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
struct Term<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    // we need clause to select box/mut selector/constructor based on sort
    clause: &'a chc::Clause,
    inner: &'a chc::Term,
}

impl<'ctx, 'a> std::fmt::Display for Term<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Term::Null => write!(f, "null"),
            chc::Term::Var(v) => write!(f, "{}", v),
            chc::Term::Int(i) => write!(f, "{}", i),
            chc::Term::Bool(b) => write!(f, "{}", b),
            chc::Term::String(s) => write!(f, "\"{}\"", s.escape_default()),
            chc::Term::Box(t) => {
                let s = self.clause.term_sort(t);
                write!(
                    f,
                    "({} {})",
                    self.ctx.box_ctor(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::Mut(t1, t2) => {
                let s = self.clause.term_sort(t1);
                write!(
                    f,
                    "({} {} {})",
                    self.ctx.mut_ctor(&s),
                    Term::new(self.ctx, self.clause, t1),
                    Term::new(self.ctx, self.clause, t2)
                )
            }
            chc::Term::BoxCurrent(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.box_current(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::MutCurrent(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.mut_current(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::MutFinal(t) => {
                let s = self.clause.term_sort(t).deref();
                write!(
                    f,
                    "({} {})",
                    self.ctx.mut_final(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::App(fn_, args) => {
                write!(
                    f,
                    "({} {})",
                    fn_,
                    List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                )
            }
            chc::Term::ArrayEmpty(index, elem) => {
                let index_sort = self.ctx.fmt_sort(index);
                let elem_sort = self.ctx.fmt_sort(elem);
                let default = chc::Term::default_for(elem);
                write!(
                    f,
                    "((as const (Array {index_sort} {elem_sort})) {})",
                    Term::new(self.ctx, self.clause, &default)
                )
            }
            chc::Term::SeqConcat(elem, t) => {
                let name = self.ctx.seq_concat(elem);
                write!(
                    f,
                    "({} {})",
                    name,
                    List::open(t.iter_args().map(|t| Term::new(self.ctx, self.clause, t)))
                )
            }
            chc::Term::Tuple(ts) => {
                let ss: Vec<_> = ts.iter().map(|t| self.clause.term_sort(t)).collect();
                if ss.is_empty() {
                    write!(f, "{}", self.ctx.tuple_ctor(&ss),)
                } else {
                    write!(
                        f,
                        "({} {})",
                        self.ctx.tuple_ctor(&ss),
                        List::open(ts.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                    )
                }
            }
            chc::Term::TupleProj(t, i) => {
                let s = self.clause.term_sort(t);
                write!(
                    f,
                    "({} {})",
                    self.ctx.tuple_proj(s.as_tuple().unwrap(), *i),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::DatatypeCtor(sort, sym, args) => {
                if args.is_empty() {
                    write!(f, "{}", self.ctx.datatype_ctor(sort, sym))
                } else {
                    write!(
                        f,
                        "({} {})",
                        self.ctx.datatype_ctor(sort, sym),
                        List::open(args.iter().map(|t| Term::new(self.ctx, self.clause, t)))
                    )
                }
            }
            chc::Term::DatatypeDiscr(_s, t) => {
                let s = self.clause.term_sort(t).into_datatype().unwrap();
                write!(
                    f,
                    "({} {})",
                    self.ctx.datatype_discr(&s),
                    Term::new(self.ctx, self.clause, t)
                )
            }
            chc::Term::FormulaQuantifiedVar(_, name) => write!(f, "{}", name),
        }
    }
}

impl<'ctx, 'a> Term<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Term) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Atom`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Atom<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Atom,
}

impl<'ctx, 'a> std::fmt::Display for Atom<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(guard) = &self.inner.guard {
            let guard = Formula::new(self.ctx, self.clause, guard);
            write!(f, "(=> {} ", guard)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, "(not ")?;
        }
        let pred = match &self.inner.pred {
            chc::Pred::Matcher(p) => self.ctx.matcher_pred(p).to_string(),
            p => p.name().into_owned(),
        };
        if self.inner.args.is_empty() {
            write!(f, "{}", pred)?;
        } else {
            let args = List::open(
                self.inner
                    .args
                    .iter()
                    .map(|t| Term::new(self.ctx, self.clause, t)),
            );
            write!(f, "({} {})", pred, args)?;
        }
        if self.inner.pred.is_negative() {
            write!(f, ")")?;
        }
        if self.inner.guard.is_some() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'ctx, 'a> Atom<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Atom) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Formula`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Formula<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Formula,
}

impl<'ctx, 'a> std::fmt::Display for Formula<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.inner {
            chc::Formula::Atom(atom) => {
                let atom = Atom::new(self.ctx, self.clause, atom);
                write!(f, "{}", atom)
            }
            chc::Formula::Not(fo) => {
                let fo = Formula::new(self.ctx, self.clause, fo);
                write!(f, "(not {})", fo)
            }
            chc::Formula::And(fs) => {
                let fs = List::open(fs.iter().map(|fo| Formula::new(self.ctx, self.clause, fo)));
                write!(f, "(and {})", fs)
            }
            chc::Formula::Or(fs) => {
                let fs = List::open(fs.iter().map(|fo| Formula::new(self.ctx, self.clause, fo)));
                write!(f, "(or {})", fs)
            }
            chc::Formula::Implies(lhs, rhs) => {
                let lhs = Formula::new(self.ctx, self.clause, lhs);
                let rhs = Formula::new(self.ctx, self.clause, rhs);
                write!(f, "(=> {lhs} {rhs})")
            }
            chc::Formula::Exists(vars, fo) => {
                let vars =
                    List::closed(vars.iter().map(|(v, s)| {
                        List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])
                    }));
                let fo = Formula::new(self.ctx, self.clause, fo);
                write!(f, "(exists {vars} {fo})")
            }
            chc::Formula::Forall(vars, fo) => {
                let vars =
                    List::closed(vars.iter().map(|(v, s)| {
                        List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])
                    }));
                let fo = Formula::new(self.ctx, self.clause, fo);
                write!(f, "(forall {vars} {fo})")
            }
        }
    }
}

impl<'ctx, 'a> Formula<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Formula) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Body`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Body<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    clause: &'a chc::Clause,
    inner: &'a chc::Body,
}

impl<'ctx, 'a> std::fmt::Display for Body<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let atoms = List::open(
            self.inner
                .atoms
                .iter()
                .map(|a| Atom::new(self.ctx, self.clause, a)),
        );
        let formula = Formula::new(self.ctx, self.clause, &self.inner.formula);
        write!(f, "(and {atoms} {formula})")
    }
}

impl<'ctx, 'a> Body<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, clause: &'a chc::Clause, inner: &'a chc::Body) -> Self {
        Self { ctx, clause, inner }
    }
}

/// A wrapper around a [`chc::Clause`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Clause<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Clause,
}

impl<'ctx, 'a> std::fmt::Display for Clause<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.inner.debug_info.is_empty() {
            writeln!(f, "{}", self.inner.debug_info.display("; "))?;
        }
        for line in equivalent_classes(self.inner) {
            writeln!(f, "{}", line)?;
        }
        let body = Body::new(self.ctx, self.inner, &self.inner.body);
        let head = Atom::new(self.ctx, self.inner, &self.inner.head);
        if !self.inner.vars.is_empty() {
            let vars = List::closed(
                self.inner
                    .vars
                    .iter_enumerated()
                    .map(|(v, s)| List::closed([v.to_string(), self.ctx.fmt_sort(s).to_string()])),
            );
            write!(f, "(forall {vars} ")?;
        }
        write!(f, "(=> {body} {head})")?;
        if !self.inner.vars.is_empty() {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl<'ctx, 'a> Clause<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Clause) -> Self {
        Self { ctx, inner }
    }
}

/// A node of the equivalence relation derived from the top-level equality atoms of a clause
/// body. Only clause variables and ground constants participate; compound terms are
/// decomposed into them via structural equality rules (see [`add_term_equality`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum EqNode {
    Var(chc::TermVarIdx),
    Const(EqConst),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum EqConst {
    Null,
    Int(i64),
    Bool(bool),
    Str(String),
}

impl EqConst {
    fn of(term: &chc::Term) -> Option<EqConst> {
        match term {
            chc::Term::Null => Some(EqConst::Null),
            chc::Term::Int(i) => Some(EqConst::Int(*i)),
            chc::Term::Bool(b) => Some(EqConst::Bool(*b)),
            chc::Term::String(s) => Some(EqConst::Str(s.clone())),
            _ => None,
        }
    }
}

/// A union-find over [`EqNode`]s.
#[derive(Default)]
struct EqUnionFind {
    parent: HashMap<EqNode, EqNode>,
}

impl EqUnionFind {
    fn new() -> Self {
        Self::default()
    }

    fn find(&mut self, node: EqNode) -> EqNode {
        if self.parent.get(&node) == Some(&node) {
            return node;
        }
        if let Some(parent) = self.parent.get(&node).cloned() {
            let root = self.find(parent);
            self.parent.insert(node, root.clone());
            return root;
        }
        self.parent.insert(node.clone(), node.clone());
        node
    }

    fn union(&mut self, a: EqNode, b: EqNode) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            // Deterministic parent: variables before constants, lower index first.
            let (parent, child) = if rank(&ra) < rank(&rb) {
                (ra, rb)
            } else {
                (rb, ra)
            };
            self.parent.insert(child, parent);
        }
    }
}

/// An ordering of [`EqNode`]s that places variables (by ascending index) before constants.
fn rank(node: &EqNode) -> (u8, usize) {
    match node {
        EqNode::Var(v) => (0, v.index()),
        EqNode::Const(_) => (1, 0),
    }
}

fn render_eq_node(node: &EqNode) -> String {
    match node {
        EqNode::Var(v) => v.to_string(),
        EqNode::Const(c) => match c {
            EqConst::Null => "null".to_owned(),
            EqConst::Int(i) => i.to_string(),
            EqConst::Bool(b) => b.to_string(),
            EqConst::Str(s) => format!("\"{}\"", s.escape_default()),
        },
    }
}

fn add_equality_atom(atom: &chc::Atom, uf: &mut EqUnionFind) {
    if atom.guard.is_some() || atom.pred != chc::KnownPred::EQUAL.into() {
        return;
    }
    let [lhs, rhs] = &atom.args[..] else {
        return;
    };
    add_term_equality(lhs, rhs, uf);
}

/// Returns the sub-term that `term` projects to when it is a datatype selector applied
/// directly to its constructor, e.g. `mut_final(mut(c, f))` projects to `f`. Selectors are
/// not injective, so no other forms are considered.
fn projected_term(term: &chc::Term) -> Option<&chc::Term> {
    match term {
        chc::Term::MutFinal(inner) => match &**inner {
            chc::Term::Mut(_, final_) => Some(final_),
            _ => None,
        },
        chc::Term::MutCurrent(inner) => match &**inner {
            chc::Term::Mut(current, _) => Some(current),
            _ => None,
        },
        chc::Term::BoxCurrent(inner) => match &**inner {
            chc::Term::Box(x) => Some(x),
            _ => None,
        },
        chc::Term::TupleProj(t, i) => match &**t {
            chc::Term::Tuple(ts) => ts.get(*i),
            _ => None,
        },
        _ => None,
    }
}

/// Decomposes an equality between two terms into elementary equivalences over clause
/// variables and ground constants. Beyond var-var/var-const equalities, structural
/// equalities are decomposed using the datatype rules: constructors are injective, and a
/// selector applied to its constructor reduces to the projected argument. All of these are
/// exact, so the resulting classes are implied by the clause's assumptions.
fn add_term_equality(lhs: &chc::Term, rhs: &chc::Term, uf: &mut EqUnionFind) {
    if let (chc::Term::Var(a), chc::Term::Var(b)) = (lhs, rhs) {
        uf.union(EqNode::Var(*a), EqNode::Var(*b));
        return;
    }
    if let Some(proj) = projected_term(lhs) {
        add_term_equality(proj, rhs, uf);
        return;
    }
    if let Some(proj) = projected_term(rhs) {
        add_term_equality(lhs, proj, uf);
        return;
    }
    match (lhs, rhs) {
        (chc::Term::Var(a), other) => {
            if let Some(c) = EqConst::of(other) {
                uf.union(EqNode::Var(*a), EqNode::Const(c));
            }
        }
        (other, chc::Term::Var(b)) => {
            if let Some(c) = EqConst::of(other) {
                uf.union(EqNode::Const(c), EqNode::Var(*b));
            }
        }
        (chc::Term::Mut(a1, a2), chc::Term::Mut(b1, b2)) => {
            add_term_equality(a1, b1, uf);
            add_term_equality(a2, b2, uf);
        }
        (chc::Term::Box(a), chc::Term::Box(b)) => add_term_equality(a, b, uf),
        (chc::Term::DatatypeCtor(_, sym1, args1), chc::Term::DatatypeCtor(_, sym2, args2))
            if sym1 == sym2 && args1.len() == args2.len() =>
        {
            for (a, b) in args1.iter().zip(args2) {
                add_term_equality(a, b, uf);
            }
        }
        _ => {}
    }
}

/// Collects the top-level (unguarded) equality atoms of a clause body into the union-find.
fn collect_top_level_equalities(body: &chc::Body, uf: &mut EqUnionFind) {
    for atom in &body.atoms {
        add_equality_atom(atom, uf);
    }
    match &body.formula {
        chc::Formula::And(fs) => {
            for fo in fs {
                if let chc::Formula::Atom(atom) = fo {
                    add_equality_atom(atom, uf);
                }
            }
        }
        fo => {
            if let chc::Formula::Atom(atom) = fo {
                add_equality_atom(atom, uf);
            }
        }
    }
}

/// Returns the equivalence classes among clause variables implied by the top-level equality
/// atoms of the body, as supplementary comment lines like `; v0=v1=v5, v7=false`. The clause
/// body itself is left untouched.
fn equivalent_classes(clause: &chc::Clause) -> Vec<String> {
    let mut uf = EqUnionFind::new();
    collect_top_level_equalities(&clause.body, &mut uf);
    if uf.parent.is_empty() {
        return Vec::new();
    }

    let nodes: Vec<EqNode> = uf.parent.keys().cloned().collect();
    let mut classes: HashMap<EqNode, Vec<EqNode>> = HashMap::new();
    for node in nodes {
        classes.entry(uf.find(node.clone())).or_default().push(node);
    }

    let mut members_list: Vec<Vec<EqNode>> = classes.into_values().collect();
    members_list.retain(|members| members.len() >= 2);
    members_list.sort_by_key(|members| members.iter().map(rank).min());

    let mut lines: Vec<String> = Vec::new();
    let mut current = String::from("; ");
    for members in members_list {
        let mut members = members;
        members.sort_by_key(rank);
        let rendered = members
            .iter()
            .map(render_eq_node)
            .collect::<Vec<_>>()
            .join("=");
        if current.len() + rendered.len() + 2 > 100 {
            lines.push(std::mem::take(&mut current));
            current.push_str("; ");
        }
        if current.len() > 2 {
            current.push_str(", ");
        }
        current.push_str(&rendered);
    }
    if current.len() > 2 {
        lines.push(current);
    }
    lines
}

/// A wrapper around a [`chc::RawCommand`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct RawCommand<'a> {
    inner: &'a chc::RawCommand,
}

impl<'a> std::fmt::Display for RawCommand<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner.command,)
    }
}

impl<'a> RawCommand<'a> {
    pub fn new(inner: &'a chc::RawCommand) -> Self {
        Self { inner }
    }
}

/// A wrapper around a [`chc::DatatypeSelector`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct DatatypeSelector<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::DatatypeSelector,
}

impl<'ctx, 'a> std::fmt::Display for DatatypeSelector<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} {})",
            &self.inner.symbol,
            self.ctx.fmt_sort(&self.inner.sort)
        )
    }
}

impl<'ctx, 'a> DatatypeSelector<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::DatatypeSelector) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a [`chc::DatatypeCtor`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct DatatypeCtor<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::DatatypeCtor,
}

impl<'ctx, 'a> std::fmt::Display for DatatypeCtor<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let selectors = self
            .inner
            .selectors
            .iter()
            .map(|s| DatatypeSelector::new(self.ctx, s));
        write!(f, "    ({} {})", &self.inner.symbol, List::open(selectors))
    }
}

impl<'ctx, 'a> DatatypeCtor<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::DatatypeCtor) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a slice of [`chc::Datatype`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct Datatypes<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a [chc::Datatype],
}

impl<'ctx, 'a> std::fmt::Display for Datatypes<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.inner.is_empty() {
            return Ok(());
        }

        let datatypes = self
            .inner
            .iter()
            .map(|d| format!("({} 0)", self.ctx.fmt_datatype_symbol(&d.symbol)));
        let ctors = self.inner.iter().map(|d| {
            format!(
                "  (par () (\n{}\n  ))",
                List::multiline_open(d.ctors.iter().map(|c| DatatypeCtor::new(self.ctx, c)))
            )
        });
        write!(
            f,
            "(declare-datatypes {} {})",
            List::closed(datatypes),
            List::multiline_closed(ctors)
        )
    }
}

impl<'ctx, 'a> Datatypes<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a [chc::Datatype]) -> Self {
        Self { ctx, inner }
    }
}

/// A wrapper around a [`chc::Datatype`] that provides a [`std::fmt::Display`] implementation for the
/// discriminant function in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct DatatypeDiscrFun<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Datatype,
}

impl<'ctx, 'a> std::fmt::Display for DatatypeDiscrFun<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sym = &self.inner.symbol;
        let cases = self
            .inner
            .ctors
            .iter()
            .rfold("(- 1)".to_owned(), |acc, ctor| {
                format!(
                    "(ite ((_ is {ctor}) x) {discr} {acc})",
                    ctor = &ctor.symbol,
                    discr = ctor.discriminant,
                )
            });
        write!(
            f,
            "(define-fun {discr} ((x {sym})) Int {cases})",
            discr = self.ctx.datatype_discr_def(sym),
            sym = self.ctx.fmt_datatype_symbol(sym),
        )
    }
}

impl<'ctx, 'a> DatatypeDiscrFun<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Datatype) -> DatatypeDiscrFun<'ctx, 'a> {
        DatatypeDiscrFun { ctx, inner }
    }
}

/// A wrapper around a [`chc::Datatype`] that provides a [`std::fmt::Display`] implementation for the
/// matcher predicate in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct MatcherPredFun<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::Datatype,
}

impl<'ctx, 'a> std::fmt::Display for MatcherPredFun<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let sym = &self.inner.symbol;
        let mut offset = 0;
        let mut variants = Vec::new();
        for ctor in &self.inner.ctors {
            let args = List::open(
                (0..ctor.selectors.len())
                    .map(|i| i + offset)
                    .map(|i| format!("x{i}")),
            );
            offset += ctor.selectors.len();
            let repr = if ctor.selectors.is_empty() {
                ctor.symbol.to_string()
            } else {
                format!("({} {})", &ctor.symbol, args)
            };
            variants.push(format!("(= v {repr})"));
        }
        let params = List::closed(
            self.inner
                .ctors
                .iter()
                .flat_map(|c| &c.selectors)
                .enumerate()
                .map(|(idx, s)| format!("(x{} {})", idx, self.ctx.fmt_sort(&s.sort)))
                .chain([format!("(v {})", self.ctx.fmt_datatype_symbol(sym))]),
        );
        write!(
            f,
            "(define-fun {name} {params} Bool (or {variants}))",
            name = self.ctx.matcher_pred_def(sym),
            variants = List::open(variants),
        )
    }
}

impl<'ctx, 'a> MatcherPredFun<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::Datatype) -> MatcherPredFun<'ctx, 'a> {
        MatcherPredFun { ctx, inner }
    }
}

pub struct UserDefinedPredDef<'ctx, 'a> {
    ctx: &'ctx FormatContext,
    inner: &'a chc::UserDefinedPredDef,
}

impl<'ctx, 'a> std::fmt::Display for UserDefinedPredDef<'ctx, 'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = List::closed(
            self.inner
                .sig
                .iter()
                .map(|(name, sort)| format!("({} {})", name, self.ctx.fmt_sort(sort))),
        );
        write!(
            f,
            "(define-fun {name} {params} Bool {body})",
            name = self.inner.symbol,
            body = &self.inner.body,
        )
    }
}

impl<'ctx, 'a> UserDefinedPredDef<'ctx, 'a> {
    pub fn new(ctx: &'ctx FormatContext, inner: &'a chc::UserDefinedPredDef) -> Self {
        Self { ctx, inner }
    }
}
/// A wrapper around a [`chc::System`] that provides a [`std::fmt::Display`] implementation in SMT-LIB2 format.
#[derive(Debug, Clone)]
pub struct System<'a> {
    ctx: FormatContext,
    inner: &'a chc::System,
}

impl<'a> std::fmt::Display for System<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(set-logic HORN)\n")?;

        writeln!(f, "{}\n", Datatypes::new(&self.ctx, self.ctx.datatypes()))?;
        for datatype in self.ctx.datatypes() {
            writeln!(f, "{}", DatatypeDiscrFun::new(&self.ctx, datatype))?;
            writeln!(f, "{}", MatcherPredFun::new(&self.ctx, datatype))?;
        }

        for elem in self.ctx.int_array_elem_sorts() {
            let name = self.ctx.seq_concat(elem);
            let elem_ty = self.ctx.fmt_sort(elem);
            // The sequences are passed as `(array, length)` tuples
            let seq_fields = [
                chc::Sort::array(chc::Sort::int(), elem.clone()),
                chc::Sort::int(),
            ];
            let seq_ty = self.ctx.fmt_sort(&chc::Sort::tuple(seq_fields.to_vec()));
            let ctor = self.ctx.tuple_ctor(&seq_fields);
            let array = self.ctx.tuple_proj(&seq_fields, 0);
            let len = self.ctx.tuple_proj(&seq_fields, 1);
            writeln!(
                f,
                "(define-fun-rec {name} \
                  ((s {seq_ty}) (t {seq_ty})) \
                  (Array Int {elem_ty}) \
                  (ite (<= ({len} t) 0) ({array} s) \
                       (store ({name} s ({ctor} ({array} t) (- ({len} t) 1))) \
                              (+ ({len} s) (- ({len} t) 1)) \
                              (select ({array} t) (- ({len} t) 1)))))\n",
            )?;
        }

        // insert command from #![thrust::raw_command()] here
        for raw_command in &self.inner.raw_commands {
            writeln!(f, "{}\n", RawCommand::new(raw_command))?;
        }

        for user_defined_pred_def in &self.inner.user_defined_pred_defs {
            writeln!(
                f,
                "{}\n",
                UserDefinedPredDef::new(&self.ctx, user_defined_pred_def)
            )?;
        }

        writeln!(f)?;
        for (p, def) in self.inner.pred_vars.iter_enumerated() {
            if !def.debug_info.is_empty() {
                writeln!(f, "{}", def.debug_info.display("; "))?;
            }
            writeln!(
                f,
                "(declare-fun {} {} Bool)\n",
                p,
                List::closed(def.sig.iter().map(|s| self.ctx.fmt_sort(s)))
            )?;
        }
        for (id, clause) in self.inner.clauses.iter_enumerated() {
            writeln!(
                f,
                "; {:?}\n(assert {})\n",
                id,
                Clause::new(&self.ctx, clause)
            )?;
        }
        Ok(())
    }
}

impl<'a> System<'a> {
    pub fn new(inner: &'a chc::System) -> Self {
        let ctx = FormatContext::from_system(inner);
        Self { ctx, inner }
    }
}
