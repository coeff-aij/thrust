//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The whole crate is verified and `user::make` names `bounds::big` in its reveal, but a reveal
// applies only to the body it is written on: `other::use_big` reads `big` without its
// definition, so `big(v)` does not give `v > 10`, as when `use_big` is verified alone.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }
}

mod user {
    #[thrust::reveal(crate::bounds::big)]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(crate::bounds::big(result))]
    pub fn make() -> i64 {
        11
    }
}

mod other {
    #[thrust_macros::requires(crate::bounds::big(v))]
    #[thrust_macros::ensures(result > 10)]
    pub fn use_big(v: i64) -> i64 {
        v
    }
}

fn main() {
    let x = user::make();
    let _ = other::use_big(x);
}
