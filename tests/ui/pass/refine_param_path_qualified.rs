//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@check-pass
use thrust_models::Model;
pub enum Pair<T> {
    Mk(T, T),
}

impl<T> Model for Pair<T> {
    type Ty = Self;
}

#[thrust_macros::param(p: crate::Pair<{ v: i32 | v > 0 }>)]
#[thrust_macros::ret({ r: i32 | r > 0 })]
fn first(p: Pair<i32>) -> i32 {
    match p {
        Pair::Mk(a, _) => a,
    }
}

fn main() {}
