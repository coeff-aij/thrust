//@compile-flags: -C debug-assertions=off

// An invariant's parameter has the type of the variable it names. `B` has `A`'s field types in
// the other order, so `p.x` of a `B` would read `A`'s `y`, and `p.x >= 0` would hold.

struct A {
    x: i64,
    y: i64,
}

impl thrust_models::Model for A {
    type Ty = A;
}

struct B {
    y: i64,
    x: i64,
}

impl thrust_models::Model for B {
    type Ty = B;
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn f(n: i64) -> i64 {
    let mut p = A { x: 0, y: 7 };
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(|p: B, i: i64| p.x >= 0 && i >= 0); //~ ERROR: loop invariant gives `p` the type `B`, but `p` at the loop header has type `A`
        p.x -= 1;
        i += 1;
    }
    p.y
}

fn main() {}
