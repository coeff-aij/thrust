//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct W<C>(C);

impl<C> thrust_models::Model for W<C> {
    type Ty = Self;
}

#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(result >= 1)]
fn g(w: &W<impl Clone>, n: i64) -> i64 {
    if n >= 0 {
        n
    } else {
        0
    }
}

fn main() {
    let w = W(1i32);
    assert!(g(&w, 0) >= 1);
}
