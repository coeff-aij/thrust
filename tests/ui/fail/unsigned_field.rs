//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct Counter {
    n: usize,
    step: i64,
}

// The field is non-negative, not positive.
fn check(c: &Counter) {
    assert!(c.n > 0);
}

fn main() {
    let c = Counter { n: 0, step: -1 };
    check(&c);
    let _ = c.step;
}
