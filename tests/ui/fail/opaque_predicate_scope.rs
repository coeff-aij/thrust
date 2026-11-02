//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The whole crate is verified and `bounds::make` reveals `big`, but a reveal applies only to the
// body it is written on: `use_big`, in another module, reads `big` without its definition, so
// `big(v)` does not give `v > 10`, as when `use_big` is verified alone.

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
}

mod user {
    #[thrust_macros::requires(crate::bounds::big(v))]
    #[thrust_macros::ensures(result > 10)]
    pub fn use_big(v: i64) -> i64 {
        v
    }
}

fn main() {
    let x = bounds::make();
    let _ = user::use_big(x);
}
