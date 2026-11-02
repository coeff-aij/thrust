//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A local moved out and assigned again in the same basic block, then read with the moved value.

struct S {
    a: i64,
}

fn f(n: i64) -> i64 {
    let mut s = S { a: n };
    let t = s;
    s = S { a: t.a + 1 };
    s.a - t.a
}

fn main() {
    assert!(f(5) == 0);
}
