//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:0360cb142

use thrust_models::model::Int;

struct Pair(i64, i64);

impl thrust_models::Model for Pair {
    type Ty = (Int, Int);
}

#[thrust_macros::context]
impl Pair {
    #[thrust_macros::logic]
    fn sum(self) -> Int {
        self.0 + self.1
    }
}

#[thrust_macros::ensures(Pair::sum(result) == Pair::sum(p) + 1)]
fn bump(p: Pair) -> Pair {
    Pair(p.0 + 2, p.1)
}

fn main() {
    let q = bump(Pair(1, 2));
    assert!(q.0 + q.1 == 4);
}
