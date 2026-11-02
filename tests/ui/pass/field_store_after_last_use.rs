//@check-pass
//@compile-flags: -C debug-assertions=off

// A field of a mutable parameter is assigned from a call's result and the parameter is not read
// afterwards: the store is in a block that does not hold the parameter.

struct A {
    x: i64,
}

fn id(x: i64) -> i64 {
    x
}

fn g(mut a: A) -> i64 {
    let old = a.x;
    a.x = id(a.x + 1);
    let _ = a.x;
    old
}

fn main() {
    assert!(g(A { x: 1 }) == 1);
}
