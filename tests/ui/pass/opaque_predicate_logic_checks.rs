//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The termination check of a logic function reads the definitions of its own module's opaque
// functions: `f` recurses only under `same(k) > 0`, which bounds the variant only by the definition of
// `same`. (`f` is opaque too: a transparent recursive definition that applies a universal
// function gets no answer from PCSat.)

mod m {
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub fn same(k: i64) -> i64 {
        k
    }

    #[thrust_macros::variant(k)]
    #[thrust_macros::logic]
    #[thrust::opaque]
    pub fn f(k: i64) -> i64 {
        if same(k) > 0 {
            f(k - 1)
        } else {
            0
        }
    }
}

#[thrust_macros::requires(m::f(k) == 0)]
#[thrust_macros::ensures(result == k)]
fn use_f(k: i64) -> i64 {
    k
}

fn main() {}
