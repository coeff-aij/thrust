//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `outer` analyzes `W::step` at `P = {closure}`, whose capture has `outer`'s second type
// parameter. The ghost term's parameter `self` has that type, so it is translated with the type
// parameters of `outer`, the owner of the instance.
use thrust_models::Ghost;

#[thrust_macros::requires(g == 1)]
fn expect_one(g: Ghost<i64>) {
    let _ = g;
}

struct W<P> {
    p: P,
    n: i64,
}

impl<P> thrust_models::Model for W<P> {
    type Ty = W<P>;
}

#[thrust_macros::context]
impl<P: FnMut(i64) -> bool> W<P> {
    fn step(&mut self) -> bool {
        let g = thrust_macros::ghost!(|self: &mut W<P>| -> i64 { (*self).n });
        expect_one(g);
        (self.p)(1)
    }
}

fn outer<U, T: Copy>(_u: U, x: T) -> bool {
    let mut w = W {
        p: move |v: i64| {
            let _y = x;
            v > 0
        },
        n: 2,
    };
    w.step()
}

fn main() {
    outer(0_i32, 3_i64);
}
