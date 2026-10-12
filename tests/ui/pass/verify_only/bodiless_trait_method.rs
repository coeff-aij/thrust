//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_VERIFY_ONLY=a

mod a {
    #[thrust_macros::requires(x >= 0)]
    #[thrust_macros::ensures(result >= 0)]
    pub fn g(x: i64) -> i64 {
        x
    }
}

mod b {
    pub trait Get {
        fn get(&self) -> i64;
    }

    pub struct One;

    impl Get for One {
        fn get(&self) -> i64 {
            1
        }
    }
}

fn main() {
    use b::Get;
    assert!(a::g(b::One.get()) >= 0);
}
