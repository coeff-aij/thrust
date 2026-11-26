//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A `post!` of a std trait method that std.rs does not specify (`Deref::deref`), at a local type
// whose impl method has no contract, takes what a call takes: the type inferred for the impl's body.
use thrust_models::Model;
use std::ops::Deref;

struct W(i32);

impl Model for W {
    type Ty = Self;
}

impl Deref for W {
    type Target = i32;

    fn deref(&self) -> &i32 {
        &self.0
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(thrust_macros::post!(<W as Deref>::deref(&w), result))]
fn f(w: &W) -> &i32 {
    w.deref()
}

fn main() {
    let w = W(1);
    let _ = f(&w);
}
