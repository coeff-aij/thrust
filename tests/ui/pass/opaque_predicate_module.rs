//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The whole crate is verified, so the bodies of `make` and `get` are analyzed; they are in the
// module of the `#[thrust::opaque]` predicate `big` and reveal it, so `big` keeps its definition,
// which their contracts need.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }

    #[thrust::reveal]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(big(result))]
    pub fn make() -> i64 {
        11
    }

    #[thrust::reveal]
    #[thrust_macros::requires(big(x))]
    #[thrust_macros::ensures(result > 10)]
    pub fn get(x: i64) -> i64 {
        x
    }
}

fn main() {
    let x = bounds::make();
    let y = bounds::get(x);
    assert!(y > 10);
}
