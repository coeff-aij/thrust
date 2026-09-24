//@error-in-other-file: Unsat

// A `Vec` reached through a field of a struct whose model is the struct itself
// keeps its real Rust type inside a formula, so the model's `.array` / `.length`
// are not spellable there. `.len()` and indexing are, and mean the same thing.

struct Rows {
    raw: Vec<i64>,
}

impl thrust_models::Model for Rows {
    type Ty = Self;
}

#[thrust_macros::ensures(result.raw.len() == 2 && result.raw[0] == a && result.raw[1] == b)]
fn pair(a: i64, b: i64) -> Rows {
    let mut raw = Vec::new();
    // Both entries get `b`, so the promised `result.raw[0] == a` is false.
    raw.push(b);
    raw.push(b);
    Rows { raw }
}

fn main() {
    let r = pair(3, 4);
    assert!(r.raw.len() == 2);
    assert!(r.raw[0] == 3);
    assert!(r.raw[1] == 4);
}
