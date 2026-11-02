//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_VERIFY_ONLY=main
// `big` is `#[thrust::opaque]` and no function that reveals it is analyzed here, so `main` reads
// it only through the contracts of `make` and `get`, which suffice.

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
