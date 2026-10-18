//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/closure_trusted_fn_ref.rs`: a capture by reference keeps its value.

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
    let y = 5;
    apply_ref(|_: &S| assert!(y == 5), &s);
}
