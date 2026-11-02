//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A parameter moved out and assigned again in the same basic block.

struct S {
    a: i64,
}

fn f(mut s: S) -> i64 {
    let t = s;
    s = S { a: t.a + 1 };
    s.a
}

fn main() {
    assert!(f(S { a: 0 }) == 0);
}
