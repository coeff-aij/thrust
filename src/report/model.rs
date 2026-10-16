//! The solver's model, read into [`Expr`]s: the interpretation of each predicate variable.

use std::collections::HashMap;

use super::expr::Expr;

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

/// The report's name for a function of the query: the selectors and constructors Thrust declares
/// for references and tuples read as the annotations write them.
fn function_name(name: &str) -> String {
    if name.starts_with("mut_current") || name.starts_with("box_current") {
        return "deref".to_owned();
    }
    if name.starts_with("mut_final") {
        return "final".to_owned();
    }
    if let Some(rest) = name.strip_prefix("tuple_proj") {
        if let Some(idx) = rest.rsplit('.').next() {
            return format!(".{idx}");
        }
    }
    if name.starts_with("mut<") {
        return "Mut::new".to_owned();
    }
    if name.starts_with("tuple<") || name == "tuple" {
        return "tuple".to_owned();
    }
    name.to_owned()
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

fn sort_name(s: &Sexp) -> String {
    match s {
        Sexp::Atom(a) => a.clone(),
        Sexp::List(items) => {
            let inner: Vec<_> = items.iter().map(sort_name).collect();
            format!("({})", inner.join(" "))
        }
    }
}

pub(super) fn to_expr(s: &Sexp) -> Expr {
    let items = match s {
        Sexp::Atom(a) => return Expr::sym(a.clone()),
        Sexp::List(items) => items,
    };
    match items.as_slice() {
        [Sexp::Atom(head), binds, body] if head == "let" => {
            let subst: HashMap<String, Expr> = bindings(binds)
                .into_iter()
                .map(|(name, value)| (name, to_expr(value)))
                .collect();
            to_expr(body).subst(&subst)
        }
        [Sexp::Atom(head), binds, body] if head == "forall" || head == "exists" => {
            let vars = bindings(binds)
                .into_iter()
                .map(|(name, sort)| (name, sort_name(sort)))
                .collect();
            let q = if head == "forall" { "forall" } else { "exists" };
            Expr::Quant(q, vars, Box::new(to_expr(body)))
        }
        [Sexp::Atom(head), args @ ..] => {
            Expr::app(function_name(head), args.iter().map(to_expr).collect())
        }
        [Sexp::List(head), args @ ..] => match head.as_slice() {
            [Sexp::Atom(u), Sexp::Atom(is), Sexp::Atom(ctor)] if u == "_" && is == "is" => {
                Expr::app(format!("is_{ctor}"), args.iter().map(to_expr).collect())
            }
            _ => Expr::app(
                sort_name(&Sexp::List(head.clone())),
                args.iter().map(to_expr).collect(),
            ),
        },
        [] => Expr::sym("()"),
    }
}

/// The interpretation of one predicate variable: its parameters and its body over them.
#[derive(Debug, Clone)]
pub struct Interpretation {
    pub params: Vec<String>,
    pub body: Expr,
}

impl Interpretation {
    /// The body with the parameters replaced by `args`.
    pub fn apply(&self, args: &[Expr]) -> Expr {
        let subst = self
            .params
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        self.body.subst(&subst).normalize()
    }
}

/// The `define-fun`s of a model as `z3` prints it after `(get-model)`, by name.
pub fn read(model: &str) -> HashMap<String, Interpretation> {
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
                    let params = bindings(params).into_iter().map(|(p, _)| p).collect();
                    let interpretation = Interpretation {
                        params,
                        body: to_expr(body),
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

    #[test]
    fn reads_define_funs() {
        let model = "(\n  (define-fun p0 ((x!0 Int) (x!1 Int)) Bool\n    (let ((a!1 (+ x!1 1))) (and (>= x!0 0) (= x!0 a!1))))\n  (define-fun p1 () Bool true)\n)";
        let model = read(model);
        let p0 = &model["p0"];
        assert_eq!(p0.params, vec!["x!0", "x!1"]);
        let applied = p0.apply(&[Expr::sym("result"), Expr::sym("x")]);
        assert_eq!(applied.to_string(), "result >= 0 && result == x + 1");
        assert!(model["p1"].body.is_true());
    }

    #[test]
    fn reads_reference_selectors() {
        let model = "((define-fun p2 ((x!0 A0_Mut<Int>)) Bool (= (mut_final<Int> x!0) (+ (mut_current<Int> x!0) 1))))";
        let model = read(model);
        let applied = model["p2"].apply(&[Expr::sym("r")]);
        assert_eq!(applied.to_string(), "!r == *r + 1");
    }
}
