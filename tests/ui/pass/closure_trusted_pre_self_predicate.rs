//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The case study's form: `Self::pred(..)` of a generic impl whose parameter is the closure's
// type states its `pre!`.

pub struct S<F>(F);

#[thrust_macros::context]
impl<F: Fn(i32)> S<F> {
    #[thrust_macros::predicate]
    fn ok(f: F, x: i32) -> bool {
        thrust_macros::pre!(f(x))
    }

    #[thrust::trusted]
    #[thrust_macros::requires(Self::ok(f, x))]
    #[thrust_macros::ensures(true)]
    fn apply(f: F, x: i32) {
        f(x)
    }
}

fn main() {
    S::apply(|x: i32| assert!(x > 0), 1);
}
