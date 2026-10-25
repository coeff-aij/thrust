//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A derived `Default` builds `D` from its fields' defaults, which break the invariant: a derived
// method that would promise it is rejected.
#[derive(Default)] //~ ERROR: which the derive does not keep
struct D {
    n: u32,
}
impl thrust_models::Model for D {
    type Ty = Self;
}
#[thrust_macros::context]
impl Invariant for D {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 1
    }
}
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result % 2 == 1)]
fn get(d: &D) -> u32 {
    d.n
}
fn main() {
    let d = D::default();
    let r = get(&d);
    assert!(r % 2 == 1);
}
