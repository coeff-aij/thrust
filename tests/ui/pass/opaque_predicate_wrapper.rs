//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A revealing body reads an opaque function's definition also through a transparent predicate
// that applies it: `make` proves `big2(11)`, which holds only by the definition of `big`.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }

    #[thrust_macros::predicate]
    pub fn big2(x: i64) -> bool {
        big(x)
    }

    #[thrust::reveal]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(big2(result))]
    pub fn make() -> i64 {
        11
    }
}

fn main() {
    let _ = bounds::make();
}
