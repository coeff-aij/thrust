//! SMT-LIB's concrete syntax: its lexemes, and the s-expressions they make, to read what a solver
//! prints besides its verdict and the commands of a query.

/// An s-expression: an atom (a symbol, with its `|` quotes removed, a numeral, a string literal
/// with its quotes, a keyword) or a list.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

/// What a span of SMT-LIB text is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lexeme {
    Open,
    Close,
    /// From `;` to the end of the line.
    Comment,
    /// A string, where `""` is an escaped quote, or a `|`-quoted symbol.
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

/// The end of the literal `bytes[start]` opens, after its closing quote; one left open runs to
/// the end.
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
pub fn lexemes(text: &str) -> Vec<(Lexeme, std::ops::Range<usize>)> {
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

enum Token {
    Open,
    Close,
    Atom(String),
}

fn tokens(text: &str) -> Vec<Token> {
    let atom = |lexeme, s: &str| match lexeme {
        Lexeme::Literal if s.starts_with('|') => {
            let quoted = &s[1..];
            quoted.strip_suffix('|').unwrap_or(quoted).to_owned()
        }
        _ => s.to_owned(),
    };
    lexemes(text)
        .into_iter()
        .filter_map(|(lexeme, span)| match lexeme {
            Lexeme::Open => Some(Token::Open),
            Lexeme::Close => Some(Token::Close),
            Lexeme::Comment | Lexeme::Space => None,
            Lexeme::Literal | Lexeme::Symbol => Some(Token::Atom(atom(lexeme, &text[span]))),
        })
        .collect()
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

    pub fn list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::Atom(_) => None,
            Sexp::List(items) => Some(items),
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
    fn skips_comments_and_reads_escaped_quotes() {
        let all = parse_all("(h ; (c\n \"a\"\"b\")");
        assert_eq!(all[0].to_string(), "(h \"a\"\"b\")");
    }
}
