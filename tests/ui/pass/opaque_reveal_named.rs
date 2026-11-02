//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `#[thrust::reveal(path, ..)]` names the opaque functions it reveals, from any module that sees
// them: `user::make` reveals `bounds::big` and the associated `Shape::wide` of another module.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }
}

mod shapes {
    pub struct Shape;

    #[thrust_macros::context]
    impl Shape {
        #[thrust_macros::predicate]
        #[thrust::opaque]
        pub fn wide(x: i64) -> bool {
            x > 5
        }
    }
}

mod user {
    #[thrust::reveal(crate::bounds::big, crate::shapes::Shape::wide)]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(crate::bounds::big(result) && crate::shapes::Shape::wide(result))]
    pub fn make() -> i64 {
        11
    }
}

fn main() {
    let _ = user::make();
}
