//! S-expressions in SMT-LIB's concrete syntax, to read what a solver prints besides its verdict
//! and the raw texts of a query (see [`super::raw_symbols`]).

/// An s-expression: an atom (a symbol, with its `|` quotes removed, a numeral, a string literal
/// with its quotes, a keyword) or a list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

enum Token {
    Open,
    Close,
    Atom(String),
}

fn tokens(text: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut chars = text.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            '(' => {
                tokens.push(Token::Open);
                chars.next();
            }
            ')' => {
                tokens.push(Token::Close);
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            ';' => {
                chars.by_ref().take_while(|&c| c != '\n').for_each(drop);
            }
            '|' => {
                chars.next();
                let quoted: String = chars.by_ref().take_while(|&c| c != '|').collect();
                tokens.push(Token::Atom(quoted));
            }
            '"' => {
                chars.next();
                let quoted: String = chars.by_ref().take_while(|&c| c != '"').collect();
                tokens.push(Token::Atom(format!("\"{quoted}\"")));
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
                tokens.push(Token::Atom(atom));
            }
        }
    }
    tokens
}

/// The s-expression starting at `tokens[*pos]`; `None` at a `)` or where the text ends first.
fn parse(tokens: &[Token], pos: &mut usize) -> Option<Sexp> {
    let token = tokens.get(*pos)?;
    *pos += 1;
    match token {
        Token::Open => {
            let mut items = Vec::new();
            loop {
                if let Token::Close = tokens.get(*pos)? {
                    *pos += 1;
                    return Some(Sexp::List(items));
                }
                items.push(parse(tokens, pos)?);
            }
        }
        Token::Close => None,
        Token::Atom(atom) => Some(Sexp::Atom(atom.clone())),
    }
}

/// The s-expressions of `text`, in order, without a last one the text cuts off.
pub fn parse_all(text: &str) -> Vec<Sexp> {
    let tokens = tokens(text);
    let mut pos = 0;
    let mut all = Vec::new();
    while pos < tokens.len() {
        all.extend(parse(&tokens, &mut pos));
    }
    all
}

impl Sexp {
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(a) => Some(a),
            Sexp::List(_) => None,
        }
    }

    /// Whether this is the solver's report of an error, `(error "...")`.
    pub fn is_error(&self) -> bool {
        matches!(self, Sexp::List(items) if items.first().and_then(Sexp::atom) == Some("error"))
    }

    /// The pairs `((name value) ...)` this list binds, as a `let` or a quantifier does.
    pub fn bindings(&self) -> Vec<(&str, &Sexp)> {
        let Sexp::List(items) = self else {
            return Vec::new();
        };
        items
            .iter()
            .filter_map(|b| match b {
                Sexp::List(pair) => match pair.as_slice() {
                    [Sexp::Atom(name), value] => Some((name.as_str(), value)),
                    _ => None,
                },
                Sexp::Atom(_) => None,
            })
            .collect()
    }
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sexp::Atom(a)
                if !a.starts_with('"')
                    && a.contains(|c: char| c.is_whitespace() || "()".contains(c)) =>
            {
                write!(f, "|{a}|")
            }
            Sexp::Atom(a) => f.write_str(a),
            Sexp::List(items) => {
                f.write_str("(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_quoted_symbols_and_strings() {
        let all = parse_all("(f |a b| \"c d\" 12) (error \"x\") (g");
        assert_eq!(all.len(), 2);
        assert_eq!(all[0].to_string(), "(f |a b| \"c d\" 12)");
        assert!(all[1].is_error());
    }

    #[test]
    fn skips_comments() {
        let all = parse_all("; a (comment\n(f |;| \";\") ; (g)\n(h)");
        assert_eq!(all.len(), 2);
        assert_eq!(all[0].to_string(), "(f ; \";\")");
    }
}
