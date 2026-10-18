//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// A closure taking a reference, handed to a trusted function that states no `pre!` of it.

struct S;

impl thrust_models::Model for S {
    type Ty = Self;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply_ref<F: Fn(&S)>(f: F, s: &S) {
    f(s)
}

fn main() {
    let s = S;
    apply_ref(|_: &S| assert!(false), &s);
}
