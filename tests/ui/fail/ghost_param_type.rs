//@compile-flags: -C debug-assertions=off

// A ghost term's parameter has the type of the variable it names. `B` has `A`'s field types in
// the other order, so `p.x` of a `B` would read `A`'s `y`, and `g == 7` would hold.

use thrust_models::model::Int;

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

fn main() {
    let p = A { x: 0, y: 7 };
    let g = thrust_macros::ghost!(|p: B| -> Int { p.x }); //~ ERROR: ghost! gives `p` the type `B`, but it has the type `A` here
    thrust_macros::proof_assert!(|g: thrust_models::Ghost<Int>| g == 7);
    let _ = p.x;
}
