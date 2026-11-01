//@compile-flags: -C debug-assertions=off

// An invariant's parameter written `&dyn Tr` is compared with the type of the variable it names;
// the message prints it as written.

trait Tr {}

struct A {
    x: i64,
}

impl thrust_models::Model for A {
    type Ty = A;
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 0)]
fn f(n: i64) -> i64 {
    let mut p = A { x: 0 };
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(|p: &dyn Tr, i: i64| i >= 0); //~ ERROR: loop invariant gives `p` the type `&dyn Tr`, but `p` at the loop header has type `A`
        p.x -= 1;
        i += 1;
    }
    p.x
}

fn main() {}
