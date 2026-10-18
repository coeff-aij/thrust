//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/lemma_trait_impl.rs`: an impl's definition of a trait's lemma is a
// lemma, which `proof!` calls through the trait.

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
    #[thrust_macros::lemma]
    #[thrust_macros::requires(x == 0)]
    #[thrust_macros::ensures(x == 0)]
    fn h(x: i64) {}
}

fn main() {
    let x = 0;
    thrust_macros::proof!(<X as Helper>::h(x));
    assert!(x == 0);
}
