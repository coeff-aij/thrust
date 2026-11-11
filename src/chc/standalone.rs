//! The query of a part (`THRUST_SPLIT`) made to depend on the part alone: it declares only what
//! its assertions need, and the names Thrust numbers across the crate are numbered within it, so
//! that the solver reads no more than the part and the text, the key of `THRUST_CACHE_DIR`, stays
//! the same while the rest of the crate changes.
//!
//! The printed query is read as the graph of its top-level commands.
//!
//! - Pruning. A declaration (of a sort, of a group of datatypes with their constructors,
//!   selectors and testers, of a function, a definition or an unknown, of a universal function
//!   with its law) is kept when a kept command names a symbol it declares; the candidate atoms of
//!   an unknown are kept with the unknown; every other command (an assertion, `set-logic`, a raw
//!   command) is kept. A command names each of its symbols and each piece of a symbol between `<`,
//!   `-` and `>`, so that a symbol built from a sort's name (`A1_Tuple<Seq<a3>-Int>`,
//!   `q_len_…<a3>`) keeps the sort's declaration. No kept command names a symbol of a declaration
//!   left out, so the kept commands say of their symbols what they said in the whole query. A
//!   declaration left out constrains nothing kept: a sort, a datatype, a definition and an
//!   unknown constrain only their own symbols, and the law of a universal function is a premise of
//!   the clauses that apply the function (fptprove's `:law`), none of which is kept. The query
//!   left is satisfiable exactly when the whole one is. This is the reachability pruning of
//!   Boogie (`/prune`, `Source/VCGeneration/Prune/Pruner.cs`) and Verus
//!   (`source/vir/src/prune.rs`), where an axiom stands on its own and is kept when it mentions
//!   a symbol kept; here every law belongs to the universal function it is declared with.
//! - Renumbering. The forall sorts `a<n>` (also as a piece of a symbol, and in the
//!   `default_a<n>` of a sort's padding) and the quantified variables `q$<n>` are numbered across
//!   the crate. Each is renumbered in the order its name first occurs outside comments, skipping
//!   a number whose name the query uses otherwise, and renamed wherever it occurs, comments
//!   included. The renaming is one-to-one, of universally quantified sorts and bound variables,
//!   so the query means what it meant. The unknowns `p<n>` keep their numbers, by which the
//!   solver's models and refutations are read; the cache key renumbers them
//!   ([`super::cache::canonical`]). An answer is read only from `z3`, which reads no forall sort,
//!   and a quantified variable in it is read by its binder, so no answer needs a name mapped back.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use super::sexp::{self, Sexp};

/// `query`, the printed query of a part, with the declarations nothing in it needs left out and
/// its names numbered within it (see the module documentation).
pub fn standalone_query(query: &str) -> String {
    let (commands, rest) = commands(query);
    let kept = kept(&commands);
    let mut pruned = String::with_capacity(query.len());
    let mut forall_sorts = HashSet::new();
    for (command, _) in commands.iter().zip(&kept).filter(|(_, &kept)| kept) {
        pruned.push_str(&query[command.span.clone()]);
        if let Some(sort) = command.declared_forall_sort() {
            forall_sorts.insert(sort);
        }
    }
    pruned.push_str(rest);
    renumbered(&pruned, &forall_sorts)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Lexeme {
    Open,
    Close,
    /// From `;` to the end of the line.
    Comment,
    /// A string or a `|`-quoted symbol.
    Literal,
    Symbol,
    Space,
}

fn is_delimiter(b: u8) -> bool {
    b.is_ascii_whitespace() || matches!(b, b'(' | b')' | b';' | b'"' | b'|')
}

/// The first index from `start` whose byte `stop` holds, or the end.
fn run_end(bytes: &[u8], start: usize, stop: impl Fn(u8) -> bool) -> usize {
    bytes[start..]
        .iter()
        .position(|&b| stop(b))
        .map_or(bytes.len(), |n| start + n)
}

/// The end of the literal `bytes[start]` opens: after its closing quote, where in a string `""`
/// is an escaped quote. A literal left open runs to the end.
fn literal_end(bytes: &[u8], start: usize) -> usize {
    let quote = bytes[start];
    let mut i = start + 1;
    while i < bytes.len() {
        if bytes[i] != quote {
            i += 1;
        } else if quote == b'"' && bytes.get(i + 1) == Some(&b'"') {
            i += 2;
        } else {
            return i + 1;
        }
    }
    bytes.len()
}

/// The lexemes of `text` with their spans. Every delimiter is ASCII, so a span never splits a
/// character.
fn lexemes(text: &str) -> Vec<(Lexeme, Range<usize>)> {
    let bytes = text.as_bytes();
    let mut lexemes = Vec::new();
    let mut start = 0;
    while start < bytes.len() {
        let (lexeme, end) = match bytes[start] {
            b'(' => (Lexeme::Open, start + 1),
            b')' => (Lexeme::Close, start + 1),
            b';' => (Lexeme::Comment, run_end(bytes, start, |b| b == b'\n')),
            b'"' | b'|' => (Lexeme::Literal, literal_end(bytes, start)),
            b if b.is_ascii_whitespace() => (
                Lexeme::Space,
                run_end(bytes, start, |b| !b.is_ascii_whitespace()),
            ),
            _ => (Lexeme::Symbol, run_end(bytes, start, is_delimiter)),
        };
        lexemes.push((lexeme, start..end));
        start = end;
    }
    lexemes
}

/// A top-level command of a query.
struct Command {
    /// The command with the comments and the blank lines before it.
    span: Range<usize>,
    sexp: Sexp,
}

/// The top-level commands of `query`, and the text after the last.
fn commands(query: &str) -> (Vec<Command>, &str) {
    let mut commands = Vec::new();
    let mut start = 0;
    let mut open = 0;
    let mut depth = 0usize;
    for (lexeme, span) in lexemes(query) {
        match lexeme {
            Lexeme::Open if depth == 0 => {
                open = span.start;
                depth = 1;
            }
            Lexeme::Open => depth += 1,
            Lexeme::Close if depth == 1 => {
                let sexp = sexp::parse_all(&query[open..span.end]).remove(0);
                commands.push(Command {
                    span: start..span.end,
                    sexp,
                });
                start = span.end;
                depth = 0;
            }
            Lexeme::Close => depth -= 1,
            _ => {}
        }
    }
    (commands, &query[start..])
}

/// The commands that declare a single symbol, named right after the command's name.
const DECLARATIONS: &[&str] = &[
    "declare-sort",
    "declare-forall-sort",
    "define-sort",
    "declare-const",
    "define-const",
    "declare-fun",
    "declare-forall-fun",
    "declare-dep-exists-fun",
    "define-fun",
    "define-fun-rec",
];

/// When a command is kept.
#[derive(Debug, PartialEq, Eq)]
enum Keep {
    Always,
    /// When a kept command names one of these: the symbols the command declares, or the unknown
    /// whose candidate atoms it gives.
    With(Vec<String>),
}

impl Command {
    fn items(&self) -> &[Sexp] {
        match &self.sexp {
            Sexp::List(items) => items,
            Sexp::Atom(_) => &[],
        }
    }

    fn keep(&self) -> Keep {
        let items = self.items();
        let head = items.first().and_then(Sexp::atom);
        let second = items.get(1);
        match (head, second) {
            (Some("declare-datatypes"), Some(Sexp::List(sorts))) => {
                Keep::With(datatype_symbols(sorts, items.get(2)))
            }
            (Some(head), Some(Sexp::Atom(name))) if DECLARATIONS.contains(&head) => {
                Keep::With(vec![name.clone()])
            }
            (Some("set-info"), Some(Sexp::Atom(key))) if key == ":candidates" => {
                match items.get(2).and_then(Sexp::list).and_then(|c| c.first()) {
                    Some(Sexp::Atom(pred)) => Keep::With(vec![pred.clone()]),
                    _ => Keep::Always,
                }
            }
            _ => Keep::Always,
        }
    }

    fn declared_forall_sort(&self) -> Option<String> {
        match self.items() {
            [Sexp::Atom(head), Sexp::Atom(sort)] if head == "declare-forall-sort" => {
                Some(sort.clone())
            }
            _ => None,
        }
    }
}

/// The datatypes `(Name arity)` of `sorts`, and the constructors and selectors `decls` gives
/// them, each `(par (params) (ctors))` or `(ctors)`.
fn datatype_symbols(sorts: &[Sexp], decls: Option<&Sexp>) -> Vec<String> {
    let mut symbols: Vec<String> = sorts
        .iter()
        .filter_map(|sort| sort.list()?.first()?.atom().map(str::to_owned))
        .collect();
    let decls = decls.and_then(Sexp::list).unwrap_or_default();
    for decl in decls {
        let ctors = match decl.list().unwrap_or_default() {
            [Sexp::Atom(par), _, Sexp::List(ctors)] if par == "par" => ctors.as_slice(),
            ctors => ctors,
        };
        for ctor in ctors {
            match ctor {
                Sexp::Atom(name) => symbols.push(name.clone()),
                Sexp::List(items) => symbols.extend(
                    items
                        .iter()
                        .enumerate()
                        .filter_map(|(i, item)| match i {
                            0 => item.atom(),
                            _ => item.list()?.first()?.atom(),
                        })
                        .map(str::to_owned),
                ),
            }
        }
    }
    symbols
}

fn is_piece_delimiter(c: char) -> bool {
    matches!(c, '<' | '>' | '-')
}

/// The symbols `sexp` names, each whole and by its pieces between `<`, `-` and `>`; a string is
/// no symbol.
fn named<'a>(sexp: &'a Sexp, out: &mut Vec<&'a str>) {
    match sexp {
        Sexp::Atom(atom) if atom.starts_with('"') => {}
        Sexp::Atom(atom) => {
            out.push(atom);
            if atom.contains(is_piece_delimiter) {
                out.extend(atom.split(is_piece_delimiter).filter(|p| !p.is_empty()));
            }
        }
        Sexp::List(items) => items.iter().for_each(|item| named(item, out)),
    }
}

/// Which of `commands` are kept: those kept always, and those a kept command names a symbol of.
fn kept(commands: &[Command]) -> Vec<bool> {
    let keeps: Vec<Keep> = commands.iter().map(Command::keep).collect();
    let mut kept = vec![false; commands.len()];
    let mut pending = Vec::new();
    let mut keepers: HashMap<&str, Vec<usize>> = HashMap::new();
    for (i, keep) in keeps.iter().enumerate() {
        match keep {
            Keep::Always => {
                kept[i] = true;
                pending.push(i);
            }
            Keep::With(symbols) => {
                for symbol in symbols {
                    keepers.entry(symbol).or_default().push(i);
                }
            }
        }
    }
    let mut names = Vec::new();
    while let Some(i) = pending.pop() {
        names.clear();
        named(&commands[i].sexp, &mut names);
        for name in &names {
            for &j in keepers.get(name).into_iter().flatten() {
                if !kept[j] {
                    kept[j] = true;
                    pending.push(j);
                }
            }
        }
    }
    kept
}

/// Whether `name` is `prefix` followed by a number.
fn is_numbered(name: &str, prefix: &str) -> bool {
    name.strip_prefix(prefix)
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// The pieces of `text` and the text between them: runs without whitespace, parentheses, `<`, `-`
/// or `>`, each paired with whether it is a piece.
fn pieces(text: &str) -> impl Iterator<Item = (&str, bool)> {
    let is_delimiter = |c: char| c.is_whitespace() || c == '(' || c == ')' || is_piece_delimiter(c);
    let mut rest = text;
    std::iter::from_fn(move || {
        let first = rest.chars().next()?;
        let piece = !is_delimiter(first);
        let len = rest
            .find(|c: char| is_delimiter(c) == piece)
            .unwrap_or(rest.len());
        let (run, after) = rest.split_at(len);
        rest = after;
        Some((run, piece))
    })
}

/// The new names of the forall sorts `forall_sorts` (with their `default_` paddings) and of the
/// quantified variables, numbered in the order the pieces of `symbols` give them first.
fn renaming<'a>(
    symbols: impl Iterator<Item = &'a str> + Clone,
    forall_sorts: &HashSet<String>,
) -> HashMap<String, String> {
    let pieces = symbols.flat_map(|s| s.split(is_piece_delimiter));
    let taken: HashSet<&str> = pieces
        .clone()
        .filter(|p| is_numbered(p, "a") && !forall_sorts.contains(*p))
        .collect();
    let mut renaming = HashMap::new();
    let mut sorts = (0..)
        .map(|n| format!("a{n}"))
        .filter(|name| !taken.contains(name.as_str()));
    let mut vars = (0..).map(|n| format!("q${n}"));
    for piece in pieces {
        let sort = Some(piece)
            .filter(|p| forall_sorts.contains(*p))
            .or_else(|| {
                piece
                    .strip_prefix("default_")
                    .filter(|p| forall_sorts.contains(*p))
            });
        if let Some(sort) = sort {
            if !renaming.contains_key(sort) {
                let name = sorts.next().unwrap();
                renaming.insert(format!("default_{sort}"), format!("default_{name}"));
                renaming.insert(sort.to_owned(), name);
            }
        } else if is_numbered(piece, "q$") && !renaming.contains_key(piece) {
            renaming.insert(piece.to_owned(), vars.next().unwrap());
        }
    }
    renaming
}

/// `text` with its forall sorts, `forall_sorts`, and its quantified variables renumbered (see
/// the module documentation).
fn renumbered(text: &str, forall_sorts: &HashSet<String>) -> String {
    let lexemes = lexemes(text);
    let symbols = lexemes
        .iter()
        .filter(|(lexeme, _)| *lexeme == Lexeme::Symbol)
        .map(|(_, span)| &text[span.clone()]);
    let renaming = renaming(symbols, forall_sorts);
    let mut out = String::with_capacity(text.len());
    for (lexeme, span) in lexemes {
        let run = &text[span];
        if !matches!(lexeme, Lexeme::Symbol | Lexeme::Comment) {
            out.push_str(run);
            continue;
        }
        for (piece, is_piece) in pieces(run) {
            match renaming.get(piece).filter(|_| is_piece) {
                Some(name) => out.push_str(name),
                None => out.push_str(piece),
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kept_commands(query: &str) -> Vec<String> {
        let (commands, _) = commands(query);
        let kept = kept(&commands);
        commands
            .iter()
            .zip(kept)
            .filter(|(_, kept)| *kept)
            .map(|(c, _)| query[c.span.clone()].trim().to_owned())
            .collect()
    }

    #[test]
    fn keeps_what_the_assertions_reach() {
        let query = "(set-logic HORN)
(declare-forall-sort a1)
(declare-forall-sort a2)
(declare-datatypes ((D<a1> 0)) ((par () ((d<a1> (d_get a1))))))
(declare-datatypes ((E 0)) ((par () ((e (e_d D<a1>))))))
(declare-datatypes ((F 0)) ((par () ((f (f_x Int))))))
(define-fun g ((x E)) Bool ((_ is e) x))
(define-fun unused ((x F)) Bool true)
(declare-forall-fun q<a2> (Int) Bool :law (forall ((q$5 Int)) (q<a2> q$5)))
(declare-fun p0 (E) Bool)
(assert (forall ((v E)) (=> (g v) (p0 v))))
";
        assert_eq!(
            kept_commands(query),
            vec![
                "(set-logic HORN)",
                "(declare-forall-sort a1)",
                "(declare-datatypes ((D<a1> 0)) ((par () ((d<a1> (d_get a1))))))",
                "(declare-datatypes ((E 0)) ((par () ((e (e_d D<a1>))))))",
                "(define-fun g ((x E)) Bool ((_ is e) x))",
                "(declare-fun p0 (E) Bool)",
                "(assert (forall ((v E)) (=> (g v) (p0 v))))",
            ]
        );
    }

    #[test]
    fn a_selector_keeps_its_datatype_and_a_law_its_symbols() {
        let query = "(declare-datatypes ((T 0)) ((par () ((t (t_0 Int))))))
(declare-forall-fun r (Int) Bool)
(declare-forall-fun q (Int) Bool :law (forall ((x Int)) (r x)))
(declare-dep-exists-fun p1 (q) (Int) Bool)
(set-info :candidates (p1 ((x Int)) ((q x))))
(set-info :candidates (p9 ((x Int)) ((r x))))
(assert (forall ((v T)) (p1 (t_0 v))))
";
        let kept = kept_commands(query);
        assert_eq!(kept.len(), 6);
        assert!(!kept.iter().any(|c| c.contains("p9")));
    }

    #[test]
    fn renumbers_sorts_and_variables_by_first_occurrence() {
        let forall_sorts = ["a7", "a3"].map(str::to_owned).into();
        let text = "; a7 = T\n(declare-forall-sort a7)\n(declare-forall-sort a3)\n\
            (declare-forall-fun default_a3 () a3)\n(declare-datatypes ((S<a3-Seq<a7>> 0)) ())\n\
            (assert (forall ((q$9 a7) (q$2 Int)) (= q$2 \"q$9 a7\")))\n";
        assert_eq!(
            renumbered(text, &forall_sorts),
            "; a0 = T\n(declare-forall-sort a0)\n(declare-forall-sort a1)\n\
            (declare-forall-fun default_a1 () a1)\n(declare-datatypes ((S<a1-Seq<a0>> 0)) ())\n\
            (assert (forall ((q$0 a0) (q$1 Int)) (= q$1 \"q$9 a7\")))\n"
        );
    }

    #[test]
    fn a_new_name_skips_one_the_query_uses_otherwise() {
        let forall_sorts = ["a4"].map(str::to_owned).into();
        let text = "(declare-forall-sort a4)\n(declare-fun Foo<a0> (a4) Bool)\n";
        assert_eq!(
            renumbered(text, &forall_sorts),
            "(declare-forall-sort a1)\n(declare-fun Foo<a0> (a1) Bool)\n"
        );
    }

    #[test]
    fn a_part_is_the_same_whatever_else_the_crate_numbers() {
        let one = "(set-logic HORN)\n(declare-forall-sort a0)\n(declare-forall-sort a5)\n\
            (declare-fun p0 ((Seq a5)) Bool)\n(assert (forall ((q$1 (Seq a5))) (p0 q$1)))\n";
        let other = "(set-logic HORN)\n(declare-forall-sort a1)\n(declare-forall-sort a6)\n\
            (declare-fun p0 ((Seq a6)) Bool)\n(assert (forall ((q$4 (Seq a6))) (p0 q$4)))\n";
        assert_eq!(standalone_query(one), standalone_query(other));
        assert_eq!(
            standalone_query(one),
            "(set-logic HORN)\n(declare-forall-sort a0)\n\
            (declare-fun p0 ((Seq a0)) Bool)\n(assert (forall ((q$0 (Seq a0))) (p0 q$0)))\n"
        );
    }
}
