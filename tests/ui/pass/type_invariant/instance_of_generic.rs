//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `W<u32>` has an invariant and `W<T>` none, so `h`'s contract has no conjunct at `T` and one at
// `T := u32`: `h` is analyzed at `u32`. Its contract is inferred there, so it can require the
// invariant of what it stores; a written contract at `T` cannot
// (`fail/type_invariant/instance_of_generic.rs`).
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
fn h<T>(w: &mut W<T>, t: T) {
    w.0 = t;
}
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result % 2 == 0)]
fn get(w: &W<u32>) -> u32 {
    w.0
}
fn main() {
    let mut w = W(2u32);
    h(&mut w, 4u32);
    let r = get(&w);
    assert!(r % 2 == 0);
}
