//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The impl outside the selection is assumed to meet the trait method's contract, and no more.

#![feature(custom_inner_attributes)]
#![thrust::verify_only("crate")]

mod b {
    #[thrust_macros::context]
    pub trait Get {
        #[thrust_macros::requires(true)]
        #[thrust_macros::ensures(result >= 0)]
        fn get(&self) -> i64 {
            0
        }
    }

    pub struct One;

    #[thrust_macros::context]
    impl Get for One {
        fn get(&self) -> i64 {
            1
        }
    }
}

fn main() {
    use b::Get;
    assert!(b::One.get() >= 0);
}
