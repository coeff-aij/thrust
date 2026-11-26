//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A function marked `#[thrust::reveal]` reveals the opaque functions of its module to the
// functions its `block_contract!`s are hoisted into as well: the `ensures` of the block needs the
// definition of `big`. `Shape::make` is a method, so its block is hoisted into an associated
// function, and `#[thrust::reveal(path)]` reveals `bounds::big` to it.

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
#[thrust::reveal]
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
    #[thrust::reveal(crate::bounds::big)]
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
