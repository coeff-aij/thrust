//@check-pass
//@compile-flags: -C debug-assertions=off

struct Counter {
    n: usize,
    step: i64,
}

fn need(_x: usize) {}

// A `usize` field read through `&` is non-negative.
fn check(c: &Counter) {
    assert!(c.n + 1 > 0);
}

// So is one read through `&mut`, and what is written back has to be.
fn bump(c: &mut Counter) {
    need(c.n);
    c.n += 1;
}

fn make(n: usize) -> Counter {
    Counter { n: n + 1, step: -1 }
}

fn main() {
    let mut c = make(1);
    check(&c);
    bump(&mut c);
    let mut d = Counter { n: 0, step: 1 };
    bump(&mut d);
    need(d.n);
    let _ = c.step + d.step;
}
