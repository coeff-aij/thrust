//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=a::**

mod a {
    #[thrust_macros::requires(x >= 0)]
    #[thrust_macros::ensures(result > x)]
    pub fn g(x: i64) -> i64 {
        inner::f(x) + 1
    }

    pub mod inner {
        #[thrust_macros::requires(x >= 0)]
        #[thrust_macros::ensures(result >= x)]
        pub fn f(x: i64) -> i64 {
            x - 1
        }
    }
}

fn main() {
    assert!(a::g(1) > 1);
}
