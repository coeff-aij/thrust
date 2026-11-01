//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A `Box` parameter moved out and assigned again by a call, with a join point after it.

fn id(x: i64) -> i64 {
    x
}

fn f(mut b: Box<i64>) -> i64 {
    let t = b;
    b = Box::new(*t + 1);
    if id(0) == 0 {}
    *b
}

fn main() {
    let r = f(Box::new(0));
    assert!(r == 0);
}
