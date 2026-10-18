//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An impl's definition of a trait's lemma that is not a lemma is not checked to terminate or to
// change nothing, and `proof!(<X as Helper>::h(x))` runs it nowhere: with `loop {}` as its body,
// any contract it states would hold.

#[thrust_macros::context]
trait Helper {
    #[thrust_macros::lemma]
    #[thrust_macros::requires(x == 0)]
    #[thrust_macros::ensures(x == 0)]
    fn h(x: i64) {}
}

struct X;

#[thrust_macros::context]
impl Helper for X {
    #[thrust_macros::requires(x == 0)]
    #[thrust_macros::ensures(x == 0)]
    fn h(x: i64) {} //~ ERROR: an impl's definition of a trait's lemma is a `#[thrust_macros::lemma]` too
}

fn main() {
    let x = 0;
    thrust_macros::proof!(<X as Helper>::h(x));
    assert!(x == 0);
}
