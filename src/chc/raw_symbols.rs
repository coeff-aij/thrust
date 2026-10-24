//! The symbols of Thrust's that the raw SMT-LIB2 of a query names: the string bodies of
//! `#[thrust_macros::predicate]`s and the `#![thrust::raw_command]`s, which Thrust copies into
//! the query without reading them.
//!
//! The names Thrust generates carry a hash of the item they come from or the sorts they stand
//! at (`q_invariant_<hash><a0>`, `tuple_proj<Int-Int>.0`), so a raw text that spells one out
//! goes stale when the item or the datatypes change, and the solver then rejects the query for
//! an unbound symbol. [`check`] finds such a name before the query is solved. A name counts as
//! Thrust's when it has a `<...>` sort decoration or a hash of 16 or more hex digits after an
//! `_` ([`Rule`]); the builtins of SMT-LIB2 have neither, and a name the text binds itself or a
//! command of the query declares is not looked at.

use std::collections::{HashMap, HashSet};

use super::sexp::{parse_all, Sexp};
use super::{System, UserDefinedPredBody};

/// What makes a name one of Thrust's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rule {
    SortDecoration,
    Hash,
}

impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::SortDecoration => f.write_str("its sort decoration"),
            Rule::Hash => f.write_str("its hash"),
        }
    }
}

/// Why a raw text of a query keeps the query from being solved.
#[derive(Debug, thiserror::Error)]
pub enum RawTextError {
    #[error(
        "{item} names `{symbol}`, which the query does not declare (a name Thrust generates, by \
         {rule})"
    )]
    Undeclared {
        /// The raw text, described for the user.
        item: String,
        symbol: String,
        rule: Rule,
    },
    #[error("{item} has no definition in the query that Thrust can read back")]
    Unreadable { item: String },
}

/// Checks that each raw text of `system` names only those symbols of Thrust's that `query`, the
/// query of `system`, declares.
pub fn check(system: &System, query: &str) -> Result<(), RawTextError> {
    let raw_defs: Vec<_> = system
        .user_defined_pred_defs
        .iter()
        .filter(|def| matches!(def.body, UserDefinedPredBody::Raw(_)))
        .collect();
    if raw_defs.is_empty() && system.raw_commands.is_empty() {
        return Ok(());
    }
    let commands = parse_all(query);
    let declared = declared_symbols(&commands);
    let definitions = definitions(&commands);
    let mut items: Vec<(String, Sexp)> = Vec::new();
    for def in raw_defs {
        let symbol = def.symbol.to_string();
        let name = def.symbol.name.clone().unwrap_or_else(|| symbol.clone());
        let item = format!("the SMT-LIB2 body of predicate `{name}`");
        // Every definition of the system is emitted (a part keeps only those it reaches).
        let Some(&definition) = definitions.get(symbol.as_str()) else {
            return Err(RawTextError::Unreadable { item });
        };
        items.push((item, definition.clone()));
    }
    for raw in &system.raw_commands {
        for command in parse_all(&raw.command) {
            items.push((describe_command(&command), command));
        }
    }
    for (item, sexp) in &items {
        if let Some((symbol, rule)) = undeclared(sexp, &declared, &mut Vec::new()) {
            return Err(RawTextError::Undeclared {
                item: item.clone(),
                symbol: symbol.to_owned(),
                rule,
            });
        }
    }
    Ok(())
}

/// The first name of Thrust's in `sexp` that is neither declared nor bound, with `bound` the
/// names bound around `sexp`.
fn undeclared<'a>(
    sexp: &'a Sexp,
    declared: &HashSet<&str>,
    bound: &mut Vec<&'a str>,
) -> Option<(&'a str, Rule)> {
    let items = match sexp {
        Sexp::Atom(atom) => {
            let known = bound.contains(&atom.as_str()) || is_declared(atom, declared);
            return rule(atom)
                .filter(|_| !known)
                .map(|rule| (atom.as_str(), rule));
        }
        Sexp::List(items) => items,
    };
    let scope = match items.as_slice() {
        [Sexp::Atom(q), Sexp::List(binders), body @ ..]
            if matches!(q.as_str(), "forall" | "exists" | "lambda") =>
        {
            Some((sorted_names(binders), binders.as_slice(), body))
        }
        [Sexp::Atom(head), Sexp::Atom(_), Sexp::List(params), rest @ ..]
            if matches!(head.as_str(), "define-fun" | "define-fun-rec") =>
        {
            Some((sorted_names(params), params.as_slice(), rest))
        }
        [Sexp::Atom(head), Sexp::List(bindings), body @ ..] if head == "let" => {
            Some((sorted_names(bindings), bindings.as_slice(), body))
        }
        [Sexp::Atom(head), term, Sexp::List(cases)] if head == "match" => {
            if let Some(found) = undeclared(term, declared, bound) {
                return Some(found);
            }
            return cases
                .iter()
                .find_map(|case| match_case(case, declared, bound));
        }
        _ => None,
    };
    let Some((names, bindings, body)) = scope else {
        return items
            .iter()
            .find_map(|item| undeclared(item, declared, bound));
    };
    // A binding's sort or term is read outside the names it binds.
    let outer = bindings
        .iter()
        .flat_map(|b| list(Some(b)).get(1..).unwrap_or_default());
    if let Some(found) = outer
        .into_iter()
        .find_map(|s| undeclared(s, declared, bound))
    {
        return Some(found);
    }
    let depth = bound.len();
    bound.extend(names);
    let found = body
        .iter()
        .find_map(|item| undeclared(item, declared, bound));
    bound.truncate(depth);
    found
}

/// A case `(pattern body)` of a `match`: the pattern's variables are bound in the body.
fn match_case<'a>(
    case: &'a Sexp,
    declared: &HashSet<&str>,
    bound: &mut Vec<&'a str>,
) -> Option<(&'a str, Rule)> {
    let [pattern, body] = list(Some(case)) else {
        return undeclared(case, declared, bound);
    };
    let (ctor, variables) = match pattern {
        Sexp::Atom(name) if is_declared(name, declared) => (Some(pattern), &[][..]),
        Sexp::Atom(_) => (None, std::slice::from_ref(pattern)),
        Sexp::List(parts) => match parts.as_slice() {
            [ctor, variables @ ..] => (Some(ctor), variables),
            [] => (None, &[][..]),
        },
    };
    if let Some(found) = ctor.and_then(|c| undeclared(c, declared, bound)) {
        return Some(found);
    }
    let depth = bound.len();
    bound.extend(variables.iter().filter_map(Sexp::atom));
    let found = undeclared(body, declared, bound);
    bound.truncate(depth);
    found
}

/// The names of `((name sort-or-term) ..)`.
fn sorted_names(bindings: &[Sexp]) -> Vec<&str> {
    bindings
        .iter()
        .filter_map(|b| list(Some(b)).first().and_then(Sexp::atom))
        .collect()
}

/// Whether `atom` is declared, or is Z3's tester `is-C` of a declared constructor `C`.
fn is_declared(atom: &str, declared: &HashSet<&str>) -> bool {
    declared.contains(atom)
        || atom
            .strip_prefix("is-")
            .is_some_and(|ctor| declared.contains(ctor))
}

/// What makes `atom` a name of Thrust's, if anything does.
fn rule(atom: &str) -> Option<Rule> {
    if atom.starts_with('"') || atom.starts_with(':') {
        return None;
    }
    if has_sort_decoration(atom) {
        return Some(Rule::SortDecoration);
    }
    has_hash(atom).then_some(Rule::Hash)
}

/// A `<` right after a symbol character, closed later, as in `tuple<Int-Int>`; a comparison
/// operator starts with its `<`.
fn has_sort_decoration(atom: &str) -> bool {
    let bytes = atom.as_bytes();
    let Some(open) = (1..bytes.len()).find(|&i| {
        bytes[i] == b'<' && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_')
    }) else {
        return false;
    };
    atom[open..].contains('>')
}

/// An `_` followed by 16 or more lowercase hex digits that end the name or a part of it.
fn has_hash(atom: &str) -> bool {
    let bytes = atom.as_bytes();
    bytes.iter().enumerate().any(|(i, &b)| {
        if b != b'_' {
            return false;
        }
        let digits = bytes[i + 1..]
            .iter()
            .take_while(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(c))
            .count();
        let ends = bytes
            .get(i + 1 + digits)
            .is_none_or(|c| !c.is_ascii_alphanumeric());
        digits >= 16 && ends
    })
}

/// The symbols the top-level `commands` declare or define.
fn declared_symbols(commands: &[Sexp]) -> HashSet<&str> {
    let mut declared = HashSet::new();
    for command in commands {
        let items = list(Some(command));
        let Some(head) = items.first().and_then(Sexp::atom) else {
            continue;
        };
        match head {
            "declare-datatypes" => {
                declared.extend(sorted_names(list(items.get(1))));
                for datatype in list(items.get(2)) {
                    declare_constructors(datatype, &mut declared);
                }
            }
            "declare-datatype" => {
                declared.extend(items.get(1).and_then(Sexp::atom));
                if let Some(datatype) = items.get(2) {
                    declare_constructors(datatype, &mut declared);
                }
            }
            "define-funs-rec" => declared.extend(sorted_names(list(items.get(1)))),
            _ if head.starts_with("declare-") || head.starts_with("define-") => {
                declared.extend(items.get(1).and_then(Sexp::atom));
            }
            _ => {}
        }
    }
    declared
}

/// The constructors and selectors of a datatype declaration, `(par (..) (ctor..))` or `(ctor..)`,
/// where a constructor is `name` or `(name (selector sort)..)`.
fn declare_constructors<'a>(datatype: &'a Sexp, declared: &mut HashSet<&'a str>) {
    let items = list(Some(datatype));
    let ctors = match items.first().and_then(Sexp::atom) {
        Some("par") => list(items.get(2)),
        _ => items,
    };
    for ctor in ctors {
        match ctor {
            Sexp::Atom(name) => {
                declared.insert(name);
            }
            Sexp::List(parts) => {
                if let [name, selectors @ ..] = parts.as_slice() {
                    declared.extend(name.atom());
                    declared.extend(sorted_names(selectors));
                }
            }
        }
    }
}

/// Each `define-fun` and `define-fun-rec` among `commands` of the form
/// `(define-fun name (params) sort body)`, by name.
fn definitions(commands: &[Sexp]) -> HashMap<&str, &Sexp> {
    let mut definitions = HashMap::new();
    for command in commands {
        if let [Sexp::Atom(head), Sexp::Atom(name), Sexp::List(_), _, _] = list(Some(command)) {
            if head == "define-fun" || head == "define-fun-rec" {
                definitions.insert(name.as_str(), command);
            }
        }
    }
    definitions
}

fn list(sexp: Option<&Sexp>) -> &[Sexp] {
    match sexp {
        Some(Sexp::List(items)) => items,
        _ => &[],
    }
}

/// A raw command, described for the user by what it declares or by its command name.
fn describe_command(command: &Sexp) -> String {
    match list(Some(command)) {
        [Sexp::Atom(head), Sexp::Atom(name), ..]
            if head.starts_with("declare-") || head.starts_with("define-") =>
        {
            format!("the raw command declaring `{name}`")
        }
        [Sexp::Atom(head), ..] => format!("a raw `{head}` command"),
        _ => "a raw command".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chc::{RawCommand, Sort, UserDefinedPred};

    const DATATYPES: &str = "(declare-datatypes ((A1_Tuple<Int-Int> 0)) ((par () ((tuple<Int-Int> \
         (tuple_proj<Int-Int>.0 Int) (tuple_proj<Int-Int>.1 Int))))))\n";

    fn undeclared_in(query: &str, text: &str) -> Option<(String, Rule)> {
        let commands = parse_all(query);
        let declared = declared_symbols(&commands);
        let text = parse_all(text);
        text.iter()
            .find_map(|s| undeclared(s, &declared, &mut Vec::new()))
            .map(|(symbol, rule)| (symbol.to_owned(), rule))
    }

    #[test]
    fn tells_generated_names_from_builtins_and_user_names() {
        for (name, expected) in [
            (
                "q_invariant_ee0fcd4f4ccedd188692f9aa4f468aed<a0>",
                Rule::SortDecoration,
            ),
            ("p_produces_11783b0b934f4f1ff60b7f99ea47217b_5", Rule::Hash),
            ("tuple_proj<Int-Int>.0", Rule::SortDecoration),
            ("mut_current<Tuple<a0-Int>>", Rule::SortDecoration),
        ] {
            assert_eq!(rule(name), Some(expected), "{name}");
        }
        for name in [
            "<",
            "<=",
            "seq.nth",
            "is_double",
            "self_",
            "a0",
            "q$26",
            "x_1234",
            "\"a<b>\"",
        ] {
            assert_eq!(rule(name), None, "{name}");
        }
    }

    #[test]
    fn collects_what_commands_declare() {
        let query = format!(
            "{DATATYPES}(declare-datatypes ((B 0)) ((b_0123456789abcdef0 (c_0123456789abcdef0 Int))))
             (declare-datatypes ((D 0)) ((() )))
             (declare-forall-fun q_p_0123456789abcdef0<a0> (a0) Bool)
             (define-funs-rec ((r_0123456789abcdef0 ((x Int)) Bool)) ((r_0123456789abcdef0 x)))
             (define-fun f ((x Int)) Bool (g_0123456789abcdef0 x))"
        );
        let commands = parse_all(&query);
        let declared = declared_symbols(&commands);
        for name in [
            "A1_Tuple<Int-Int>",
            "tuple<Int-Int>",
            "tuple_proj<Int-Int>.0",
            "tuple_proj<Int-Int>.1",
            "b_0123456789abcdef0",
            "c_0123456789abcdef0",
            "q_p_0123456789abcdef0<a0>",
            "r_0123456789abcdef0",
            "f",
        ] {
            assert!(declared.contains(name), "{name}");
        }
        assert!(!declared.contains("g_0123456789abcdef0"));
    }

    #[test]
    fn reads_testers_and_indexed_identifiers_of_declared_names() {
        for text in [
            "(is-tuple<Int-Int> p)",
            "((_ is tuple<Int-Int>) p)",
            "((_ update-field tuple_proj<Int-Int>.0) p 1)",
        ] {
            assert_eq!(undeclared_in(DATATYPES, text), None, "{text}");
        }
        assert_eq!(
            undeclared_in(DATATYPES, "(is-tuple<Int-Bool> p)"),
            Some(("is-tuple<Int-Bool>".to_owned(), Rule::SortDecoration))
        );
    }

    #[test]
    fn leaves_out_names_the_text_binds() {
        for text in [
            "(forall ((x_0123456789abcdef0 Int)) (> x_0123456789abcdef0 0))",
            "(let ((tuple<a-b> 1)) (> tuple<a-b> 0))",
            "(define-fun d ((y_0123456789abcdef0 Int)) Bool (> y_0123456789abcdef0 0))",
            "(match p (((tuple<Int-Int> v_0123456789abcdef0 w) (> v_0123456789abcdef0 w))))",
        ] {
            assert_eq!(undeclared_in(DATATYPES, text), None, "{text}");
        }
        assert_eq!(
            undeclared_in(
                DATATYPES,
                "(and (forall ((x_0123456789abcdef0 Int)) true) (> x_0123456789abcdef0 0))"
            ),
            Some(("x_0123456789abcdef0".to_owned(), Rule::Hash)),
        );
        assert_eq!(
            undeclared_in(DATATYPES, "(let ((x (s_0123456789abcdef0 1))) x)"),
            Some(("s_0123456789abcdef0".to_owned(), Rule::Hash)),
        );
    }

    #[test]
    fn checks_nothing_without_raw_texts() {
        assert!(check(&System::default(), "(assert (q_0123456789abcdef0 1)").is_ok());
    }

    #[test]
    fn checks_raw_commands() {
        let mut system = System::default();
        system.push_raw_command(RawCommand {
            command: "(define-fun is_double ((x Int) (y Int)) Bool (= (* x 2) y))".to_owned(),
        });
        system.push_raw_command(RawCommand {
            command: "(assert (is_double 1 (h_0123456789abcdef0 1)))".to_owned(),
        });
        let query = system
            .raw_commands
            .iter()
            .map(|c| c.command.as_str())
            .collect::<String>();
        let err = check(&system, &query).unwrap_err();
        assert_eq!(
            err.to_string(),
            "a raw `assert` command names `h_0123456789abcdef0`, which the query does not \
             declare (a name Thrust generates, by its hash)"
        );
    }

    #[test]
    fn checks_raw_predicate_bodies_as_emitted() {
        let mut system = System::default();
        system.push_pred_define(
            UserDefinedPred::new("p".to_owned()),
            vec![("x".to_owned(), Sort::int())],
            "(> x 0)".to_owned(),
        );
        assert!(check(&system, "(define-fun p ((x Int)) Bool (> x 0))").is_ok());
        assert!(matches!(
            check(
                &system,
                "(define-fun p ((x Int)) Bool (> x q_0123456789abcdef0))"
            ),
            Err(RawTextError::Undeclared {
                rule: Rule::Hash,
                ..
            })
        ));
        assert!(matches!(
            check(&system, "(define-fun p ((x Int)) Bool (> x 0) 1)"),
            Err(RawTextError::Unreadable { .. })
        ));
    }
}
