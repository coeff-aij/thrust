//@compile-flags: -C debug-assertions=off
// `pre!` passes each argument at the closure's argument type. `B` has `A`'s field types in the
// other order, so passing a `B` where `g` takes an `A` would read `b.y` as `a.x`.

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

#[thrust::trusted]
#[thrust_macros::requires(thrust_macros::pre!(g(b)))] //~ ERROR: `pre!` passes a value of type `B` where the callee takes `A`
#[thrust_macros::ensures(true)]
fn apply<G: Fn(A)>(g: G, b: B) {}

fn main() {
    apply(|a: A| assert!(a.x == 0), B { y: 0, x: 1 });
}
