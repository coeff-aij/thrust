//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#![feature(custom_inner_attributes)]
#![thrust::verify_only("a::g")]

mod a {
    #[thrust_macros::requires(x >= 0)]
    #[thrust_macros::ensures(result > x)]
    pub fn g(x: i64) -> i64 {
        crate::b::h(x)
    }
}

mod b {
    pub fn h(x: i64) -> i64 {
        x
    }
}

fn main() {
    assert!(a::g(1) > 1);
}
