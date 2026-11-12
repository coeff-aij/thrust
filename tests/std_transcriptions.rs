//! The std bodies the conformance tests (`tests/ui/pass/std_specs/`) transcribe are std's.
//!
//! Each transcription is preceded by a line
//! ``// std: library/<path>, `<impl header>`, `<signature>` ``. The test finds that impl in the
//! `rust-src` component of the pinned toolchain, the function with that signature inside it, and
//! checks that its body is the transcription's: comments dropped, whitespace collapsed, and std's
//! parameters (`self` included) named as the transcription names them, in order. The
//! transcription's ghost statements are dropped first: a statement that is a call of one of
//! `GHOST_MACROS`, alone or bound or assigned to a name (a loop invariant, a ghost value, an
//! assertion), which evaluates nothing of the program, as Creusot and Verus erase ghost code. The fail twins
//! break a body on purpose and are not read. No solver is involved.

use std::path::{Path, PathBuf};

/// The `thrust_macros` macros whose calls only the analysis reads: they evaluate nothing of the
/// program (`proof!` evaluates its arguments and is not one of them).
const GHOST_MACROS: &[&str] = &[
    "invariant!",
    "partial_invariant!",
    "ghost!",
    "proof_assert!",
];

fn rust_src() -> PathBuf {
    let out = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .output()
        .expect("rustc --print sysroot");
    let sysroot = String::from_utf8(out.stdout).unwrap();
    Path::new(sysroot.trim()).join("lib/rustlib/src/rust")
}

/// `text` with its comments removed; string and character literals are kept as they are.
fn strip_comments(text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::new();
    let mut i = 0;
    while i < chars.len() {
        match (chars[i], chars.get(i + 1)) {
            ('/', Some('/')) => {
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            ('/', Some('*')) => {
                let end = text_index(&chars, i + 2, "*/").expect("unterminated block comment");
                i = end + 2;
            }
            ('"', _) => {
                let start = i;
                i += 1;
                while chars[i] != '"' {
                    i += if chars[i] == '\\' { 2 } else { 1 };
                }
                i += 1;
                out.extend(&chars[start..i]);
            }
            ('\'', _) if char_literal_len(&chars[i..]).is_some() => {
                let len = char_literal_len(&chars[i..]).unwrap();
                out.extend(&chars[i..i + len]);
                i += len;
            }
            (c, _) => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}

/// The length of the character literal `chars` starts with (`'x'` or `'\x'`), if it is one and
/// not a lifetime.
fn char_literal_len(chars: &[char]) -> Option<usize> {
    match chars {
        ['\'', '\\', _, '\'', ..] => Some(4),
        ['\'', c, '\'', ..] if *c != '\\' => Some(3),
        _ => None,
    }
}

fn text_index(chars: &[char], from: usize, pat: &str) -> Option<usize> {
    let pat: Vec<char> = pat.chars().collect();
    (from..chars.len()).find(|&i| chars[i..].starts_with(&pat))
}

/// The text between the first `{` at or after `from` and its matching `}`, and the index after
/// that `}`. `text` has no comments, so braces in comments do not count.
fn block_at(text: &str, from: usize) -> (&str, usize) {
    let open = from + text[from..].find('{').expect("a block");
    let mut depth = 0;
    for (i, c) in text[open..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => depth -= 1,
            _ => {}
        }
        if depth == 0 {
            return (&text[open + 1..open + i], open + i + 1);
        }
    }
    panic!("unbalanced braces");
}

fn collapsed(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The parameter names of a signature `fn f(..) ..`, `self` for any form of the receiver.
fn param_names(signature: &str) -> Vec<String> {
    let open = signature.find('(').expect("a parameter list");
    let mut depth = 0;
    let mut params = vec![String::new()];
    for c in signature[open + 1..].chars() {
        match c {
            '(' | '<' | '[' => depth += 1,
            ')' if depth == 0 => break,
            ')' | '>' | ']' => depth -= 1,
            ',' if depth == 0 => params.push(String::new()),
            _ => {}
        }
        params.last_mut().unwrap().push(c);
    }
    params
        .iter()
        .map(|p| p.trim_start_matches(',').trim())
        .filter(|p| !p.is_empty())
        .map(|p| match p.split_once(':') {
            Some((name, _)) => name.trim().trim_start_matches("mut ").to_string(),
            None => "self".to_string(),
        })
        .collect()
}

/// `body` with each identifier in `renames` replaced.
fn renamed(body: &str, renames: &[(String, String)]) -> String {
    let mut out = String::new();
    let mut word = String::new();
    for c in body.chars().chain(std::iter::once(' ')) {
        if c.is_alphanumeric() || c == '_' {
            word.push(c);
            continue;
        }
        let replaced = renames.iter().find(|(from, _)| *from == word);
        out.push_str(replaced.map_or(word.as_str(), |(_, to)| to.as_str()));
        word.clear();
        out.push(c);
    }
    out.pop();
    out
}

struct Transcription {
    name: String,
    path: String,
    impl_header: String,
    signature: String,
    copy_signature: String,
    copy_body: String,
}

/// The transcriptions of one conformance test, each with the `// std:` line above it.
fn transcriptions(test: &str) -> Vec<Transcription> {
    let mut found = Vec::new();
    for (start, line) in test.match_indices("// std: ") {
        let line_end = start + test[start..].find('\n').unwrap();
        let fields = &test[start + line.len()..line_end];
        let (path, rest) = fields
            .split_once(", `")
            .expect("`// std: <path>, `<impl>`, `<fn>``");
        let (impl_header, rest) = rest
            .split_once("`, `")
            .expect("an impl header and a signature");
        let signature = rest.strip_suffix('`').expect("a signature in backquotes");
        let code = strip_comments(&test[line_end..]);
        let fn_at = code
            .find("fn ")
            .expect("a function after the `// std:` line");
        let (copy_body, _) = block_at(&code, fn_at);
        let body_open = fn_at + code[fn_at..].find('{').unwrap();
        let copy_signature = code[fn_at..body_open].to_string();
        let name = copy_signature[3..copy_signature.find(['<', '(']).unwrap()].to_string();
        found.push(Transcription {
            name,
            path: path.to_string(),
            impl_header: impl_header.to_string(),
            signature: signature.to_string(),
            copy_signature,
            copy_body: copy_body.to_string(),
        });
    }
    found
}

/// The body of the function with `signature` in the impl with `impl_header` of `source`.
fn std_body(source: &str, impl_header: &str, signature: &str) -> Result<String, String> {
    let source = strip_comments(source);
    let impl_at = source
        .lines()
        .scan(0, |offset, line| {
            let at = *offset;
            *offset += line.len() + 1;
            Some((at, line))
        })
        .find(|(_, line)| collapsed(line.trim_end_matches('{')) == collapsed(impl_header))
        .map(|(at, _)| at)
        .ok_or_else(|| format!("no `{impl_header}`"))?;
    let (impl_body, _) = block_at(&source, impl_at);
    let name = &signature[..signature.find(['<', '(']).unwrap()];
    let fn_at = impl_body
        .match_indices(name)
        .map(|(at, _)| at)
        .find(|&at| {
            let rest = &impl_body[at + name.len()..];
            rest.starts_with('(') || rest.starts_with('<')
        })
        .ok_or_else(|| format!("no `{name}` in `{impl_header}`"))?;
    let body_open = fn_at + impl_body[fn_at..].find('{').unwrap();
    let found = collapsed(&impl_body[fn_at..body_open]);
    if found != collapsed(signature) {
        return Err(format!("`{impl_header}` has `{found}`, not `{signature}`"));
    }
    Ok(block_at(impl_body, fn_at).0.to_string())
}

/// `body` without its ghost statements: each statement that is a call `thrust_macros::<m>(..)` of
/// a macro `m` of `GHOST_MACROS`, alone or as the value of `let [mut] <name> [: <type>] =` or
/// `<name> =`, through its `;`. A call in any other position is kept, so that the comparison with
/// std's body fails. `body` has no comments.
fn erase_ghost(body: &str) -> String {
    let mut out = String::new();
    let mut rest = body;
    while let Some(at) = rest.find("thrust_macros::") {
        let start = rest[..at].rfind([';', '{', '}']).map_or(0, |i| i + 1);
        match ghost_statement_len(&rest[at..]) {
            Some(len) if is_binding(&rest[start..at]) => {
                out.push_str(&rest[..start]);
                rest = &rest[at + len..];
            }
            _ => {
                let kept = at + "thrust_macros::".len();
                out.push_str(&rest[..kept]);
                rest = &rest[kept..];
            }
        }
    }
    out.push_str(rest);
    out
}

/// Whether `prefix`, the text of a statement before a macro call, is empty, `let [mut] <name>
/// [: <type>] =` or `<name> =`.
fn is_binding(prefix: &str) -> bool {
    let prefix = prefix.trim();
    if prefix.is_empty() {
        return true;
    }
    let Some(target) = prefix.strip_suffix('=') else {
        return false;
    };
    let target = target.trim();
    let target = match target.strip_prefix("let ") {
        Some(binding) => binding.split(':').next().unwrap().trim(),
        None => target,
    };
    let name = target.strip_prefix("mut ").unwrap_or(target).trim();
    !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// The length of the statement `call` starts with, if `call` is `thrust_macros::<m>!(..)` of a
/// macro of `GHOST_MACROS` followed by `;`: through its balanced parentheses, string literals
/// skipped, and the `;`.
fn ghost_statement_len(call: &str) -> Option<usize> {
    let name = &call["thrust_macros::".len()..];
    let macro_name = GHOST_MACROS.iter().find(|m| name.starts_with(*m))?;
    let open = "thrust_macros::".len() + macro_name.len();
    if !call[open..].starts_with('(') {
        return None;
    }
    let close = open + matching_paren(&call[open..])?;
    let after = &call[close + 1..];
    let semicolon = after.find(';')?;
    after[..semicolon]
        .trim()
        .is_empty()
        .then_some(close + 1 + semicolon + 1)
}

/// The index of the `)` that closes the `(` `text` starts with, string literals skipped.
fn matching_paren(text: &str) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut escaped = false;
    for (i, c) in text.char_indices() {
        if in_string {
            match (escaped, c) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => continue,
        }
        if depth == 0 {
            return Some(i);
        }
    }
    None
}

fn check(t: &Transcription, rust_src: &Path) -> Result<(), String> {
    let source =
        std::fs::read_to_string(rust_src.join(&t.path)).map_err(|e| format!("{}: {e}", t.path))?;
    let body = std_body(&source, &t.impl_header, &t.signature)?;
    let renames: Vec<_> = param_names(&t.signature)
        .into_iter()
        .zip(param_names(&t.copy_signature))
        .collect();
    if collapsed(&renamed(&body, &renames)) != collapsed(&erase_ghost(&t.copy_body)) {
        return Err(format!("the body of `{}` is not std's", t.name));
    }
    Ok(())
}

#[test]
fn transcriptions_are_std_bodies() {
    let rust_src = rust_src();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/ui/pass/std_specs");
    let mut checked = 0;
    let mut errors = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        let test = std::fs::read_to_string(&path).unwrap();
        for t in transcriptions(&test) {
            checked += 1;
            if let Err(e) = check(&t, &rust_src) {
                errors.push(format!("{}: {e}", path.display()));
            }
        }
    }
    assert!(checked > 0, "no transcription under {}", dir.display());
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

#[test]
fn erase_ghost_keeps_executable_code() {
    let body = "let mut s = thrust_macros::ghost!(|| -> Seq<Int> { Seq::empty() }); \
        while let Some(x) = it.next() { thrust_macros::invariant!(|s: Ghost<Seq<Int>>| (s.len() >= 0)); \
        let c = thrust_macros::closure!(|y: i64| -> i64 { y }); \
        s = thrust_macros::ghost!(|s: Ghost<Seq<Int>>| -> Seq<Int> { s }); } true";
    assert_eq!(
        collapsed(&erase_ghost(body)),
        "while let Some(x) = it.next() { let c = thrust_macros::closure!(|y: i64| -> i64 { y }); } true"
    );
}

#[test]
fn erase_ghost_keeps_calls_inside_expressions() {
    let body = "let g = (it.next(), thrust_macros::ghost!(|| -> Int { 0 })); \
        thrust_macros::proof!(lem(it.next())); \
        let s: Ghost<Int> = thrust_macros::ghost!(|| -> Int { \"(\" }); true";
    assert_eq!(
        collapsed(&erase_ghost(body)),
        "let g = (it.next(), thrust_macros::ghost!(|| -> Int { 0 })); \
         thrust_macros::proof!(lem(it.next())); true"
    );
}

#[test]
fn strip_comments_keeps_literals() {
    let code = "let s = \"a // b\"; // c\nlet c = '/'; /* d */ x";
    assert_eq!(
        strip_comments(code),
        "let s = \"a // b\"; \nlet c = '/';  x"
    );
}

#[test]
fn param_names_of_receivers() {
    assert_eq!(
        param_names("fn eq(&self, other: &Self) -> bool"),
        ["self", "other"]
    );
    assert_eq!(
        param_names("fn f<T>(mut x: Option<(T, T)>, y: &[T])"),
        ["x", "y"]
    );
}
