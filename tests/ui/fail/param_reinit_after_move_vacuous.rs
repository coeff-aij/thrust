//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A parameter moved out and assigned again no longer holds its argument after the assignment,
// also at a join point after it.

struct S {
    a: i64,
}

fn id(x: i64) -> i64 {
    x
}

fn f(mut s: S) -> i64 {
    let t = s;
    s = S { a: id(t.a + 1) };
    if id(0) == 0 {}
    s.a
}

fn main() {
    f(S { a: 0 });
    assert!(false);
}
