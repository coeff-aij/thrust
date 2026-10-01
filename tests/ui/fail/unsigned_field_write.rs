//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct Counter {
    n: usize,
}

// `n - 1` may go below zero, so the field it builds is not a `usize` value.
fn make(n: usize) -> Counter {
    Counter { n: n - 1 }
}

fn main() {
    let c = make(0);
    let _ = c.n;
}
