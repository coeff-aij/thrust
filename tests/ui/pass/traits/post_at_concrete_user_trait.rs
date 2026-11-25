//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `post!` of a user's trait method at a concrete type takes the contract of the impl for it.
use thrust_models::Model; trait Inc {
    fn inc(x: i32) -> i32;
}

struct S;

impl Model for S {
    type Ty = ();
}

#[thrust_macros::context]
impl Inc for S {
    #[thrust_macros::requires(x < 100)]
    #[thrust_macros::ensures(result == x + 1)]
    fn inc(x: i32) -> i32 {
        x + 1
    }
}

#[thrust_macros::requires(x < 100)]
#[thrust_macros::ensures(thrust_macros::post!(<S as Inc>::inc(x), result))]
fn g(x: i32) -> i32 {
    S::inc(x)
}

fn main() {
    let y = g(3);
    assert!(y == 4);
}
