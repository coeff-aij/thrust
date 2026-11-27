//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The pass file without the reveals: the `ensures` of the blocks need the definitions of the
// opaque `small` and `bounds::big`, which the hoisted functions do not see.

mod bounds {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn big(x: i64) -> bool {
        x > 10
    }
}

#[thrust_macros::predicate]
#[thrust::opaque]
fn small(x: i64) -> bool {
    x < 5
}

#[thrust_macros::context]
#[thrust_macros::requires(true)]
fn host() -> i64 {
    thrust_macros::block_contract!(
        || -> i64
            ensures(small(result)),
        { 1 }
    )
}

struct Shape;

#[thrust_macros::context]
impl Shape {
    #[thrust_macros::requires(true)]
    fn make() -> i64 {
        thrust_macros::block_contract!(
            || -> i64
                ensures(crate::bounds::big(result)),
            { 11 }
        )
    }
}

fn main() {
    let _ = host();
    let _ = Shape::make();
}
