//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A derived `clone` of a generic type keeps the invariant at an instance that has one, as a
// non-generic one does (`pass/type_invariant/derive_clone.rs`).
#[derive(Clone)]
struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = T::Ty;
}

#[thrust_macros::context]
impl Invariant for W<u32> {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self % 2 == 0
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result % 2 == 0)]
fn get(w: &W<u32>) -> u32 {
    w.0
}

fn main() {
    let w = W(2u32);
    let v = w.clone();
    assert!(get(&v) % 2 == 0);
}
