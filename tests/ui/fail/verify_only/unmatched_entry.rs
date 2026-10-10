//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#![feature(custom_inner_attributes)]
#![thrust::verify_only("aa")] //~ ERROR: selects no function

mod a {
    #[thrust_macros::requires(x >= 0)]
    #[thrust_macros::ensures(result > x)]
    pub fn g(x: i64) -> i64 {
        x
    }
}

fn main() {}
