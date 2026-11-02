//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A reveal covers the closures of the function it is written on: the closure in `make` calls
// `needs_big(11)`, whose precondition `big(11)` holds only by the definition of `big`.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }

    #[thrust_macros::requires(big(v))]
    #[thrust_macros::ensures(true)]
    pub fn needs_big(v: i64) -> i64 {
        v
    }

    #[thrust::reveal]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    pub fn make() -> i64 {
        let f = || needs_big(11);
        f()
    }
}

fn main() {
    let _ = bounds::make();
}
