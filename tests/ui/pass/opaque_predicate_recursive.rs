//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A revealing body reads the whole definition of a recursive opaque function: its defined copy
// calls itself, so `tri(n)` with `n == 2` unfolds to 3 there, while `main` reads `tri` without its definition.

mod sums {
    #[thrust_macros::variant(n)]
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub fn tri(n: i64) -> i64 {
        if n <= 0 {
            0
        } else {
            n + tri(n - 1)
        }
    }

    #[thrust::reveal]
    #[thrust_macros::requires(n == 2)]
    #[thrust_macros::ensures(result == tri(n))]
    pub fn two(n: i64) -> i64 {
        3
    }
}

fn main() {
    let _ = sums::two(2);
}
