//! The symbols of Thrust's that the raw SMT-LIB2 of a query names: the string bodies of
//! `#[thrust_macros::predicate]`s and the `#![thrust::raw_command]`s, which Thrust copies into
//! the query without reading them.
//!
//! The names Thrust generates carry a hash of the item they come from or the sorts they stand
//! at (`q_invariant_<hash><a0>`, `tuple_proj<Int-Int>.0`), so a raw text that spells one out
//! goes stale when the item or the datatypes change, and the solver then rejects the query for
//! an unbound symbol. [`check`] finds such a name before the query is solved. A name counts as
//! Thrust's when it has a `<...>` sort decoration or a hash of 16 or more hex digits after an
//! `_`; the builtins of SMT-LIB2, bound variables and the symbols a raw command declares itself
//! have neither, and are not looked at.

use std::collections::{HashMap, HashSet};

use super::sexp::{parse_all, Sexp};
use super::{System, UserDefinedPredBody};

/// A symbol of Thrust's that a raw text names and the query does not declare.
#[derive(Debug, thiserror::Error)]
#[error("{item} names `{symbol}`, which the query does not declare")]
pub struct Undeclared {
    /// The raw text, described for the user.
    pub item: String,
    pub symbol: String,
}

/// The first symbol of Thrust's that a raw text of `system` names and `query`, the query of
/// `system`, does not declare.
pub fn check(system: &System, query: &str) -> Result<(), Undeclared> {
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
    let definitions = definition_bodies(&commands);
    for def in raw_defs {
        let symbol = def.symbol.to_string();
        let Some(body) = definitions.get(symbol.as_str()) else {
            continue;
        };
        let item = || {
            let name = def.symbol.name.clone().unwrap_or(symbol.clone());
            format!("the SMT-LIB2 body of predicate `{name}`")
        };
        check_atoms(body, &declared, &item)?;
    }
    for raw in &system.raw_commands {
        for command in parse_all(&raw.command) {
            check_atoms(&command, &declared, &|| {
                format!("the raw command `{}`", command_head(&command))
            })?;
        }
    }
    Ok(())
}

fn check_atoms(
    sexp: &Sexp,
    declared: &HashSet<&str>,
    item: &dyn Fn() -> String,
) -> Result<(), Undeclared> {
    match sexp {
        Sexp::Atom(atom) if looks_generated(atom) && !declared.contains(atom.as_str()) => {
            Err(Undeclared {
                item: item(),
                symbol: atom.clone(),
            })
        }
        Sexp::Atom(_) => Ok(()),
        Sexp::List(items) => items
            .iter()
            .try_for_each(|sexp| check_atoms(sexp, declared, item)),
    }
}

/// Whether `atom` is spelled the way Thrust spells the symbols it generates.
fn looks_generated(atom: &str) -> bool {
    if atom.starts_with('"') || atom.starts_with(':') {
        return false;
    }
    has_sort_decoration(atom) || has_hash(atom)
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
        let Sexp::List(items) = command else {
            continue;
        };
        let Some(head) = items.first().and_then(Sexp::atom) else {
            continue;
        };
        match head {
            "declare-datatypes" => {
                let sorts = list(items.get(1))
                    .iter()
                    .filter_map(|s| list(Some(s)).first());
                declared.extend(sorts.filter_map(Sexp::atom));
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
            "define-funs-rec" => {
                let decls = list(items.get(1))
                    .iter()
                    .filter_map(|d| list(Some(d)).first());
                declared.extend(decls.filter_map(Sexp::atom));
            }
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
                declared.extend(parts.first().and_then(Sexp::atom));
                let selectors = parts[1..].iter().filter_map(|s| list(Some(s)).first());
                declared.extend(selectors.filter_map(Sexp::atom));
            }
        }
    }
}

/// The body of each `define-fun` and `define-fun-rec` among `commands`, by name.
fn definition_bodies(commands: &[Sexp]) -> HashMap<&str, &Sexp> {
    let mut bodies = HashMap::new();
    for command in commands {
        let Sexp::List(items) = command else {
            continue;
        };
        if let [Sexp::Atom(head), Sexp::Atom(name), _, _, body] = items.as_slice() {
            if head == "define-fun" || head == "define-fun-rec" {
                bodies.insert(name.as_str(), body);
            }
        }
    }
    bodies
}

fn list(sexp: Option<&Sexp>) -> &[Sexp] {
    match sexp {
        Some(Sexp::List(items)) => items,
        _ => &[],
    }
}

/// The command's name and the symbol it is about, as `(define-fun is_double …)`.
fn command_head(command: &Sexp) -> String {
    let words: Vec<String> = list(Some(command))
        .iter()
        .take(2)
        .map(ToString::to_string)
        .collect();
    format!("({} …)", words.join(" "))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tells_generated_names_from_builtins_and_user_names() {
        for name in [
            "q_invariant_ee0fcd4f4ccedd188692f9aa4f468aed<a0>",
            "p_produces_11783b0b934f4f1ff60b7f99ea47217b_5",
            "tuple_proj<Int-Int>.0",
            "mut_current<Tuple<a0-Int>>",
        ] {
            assert!(looks_generated(name), "{name}");
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
            assert!(!looks_generated(name), "{name}");
        }
    }

    #[test]
    fn collects_what_commands_declare() {
        let commands = parse_all(
            "(declare-datatypes ((A1_Tuple<Int-Int> 0)) ((par () ((tuple<Int-Int> \
             (tuple_proj<Int-Int>.0 Int) (tuple_proj<Int-Int>.1 Int))))))
             (declare-forall-fun q_p_0123456789abcdef0<a0> (a0) Bool)
             (define-fun f ((x Int)) Bool (g_0123456789abcdef0 x))",
        );
        let declared = declared_symbols(&commands);
        for name in [
            "A1_Tuple<Int-Int>",
            "tuple<Int-Int>",
            "tuple_proj<Int-Int>.0",
            "tuple_proj<Int-Int>.1",
            "q_p_0123456789abcdef0<a0>",
            "f",
        ] {
            assert!(declared.contains(name), "{name}");
        }
        assert!(!declared.contains("g_0123456789abcdef0"));
    }
}
