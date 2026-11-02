//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A named reveal reveals only what it names: `user::make` names `bounds::big` but not
// `shapes::Shape::wide`, so its `ensures` on `wide` is not proved.

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
    #[thrust::reveal(crate::bounds::big)]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(crate::bounds::big(result) && crate::shapes::Shape::wide(result))]
    pub fn make() -> i64 {
        11
    }
}

fn main() {
    let _ = user::make();
}
