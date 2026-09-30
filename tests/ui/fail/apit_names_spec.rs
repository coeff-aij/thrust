//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

#[thrust_macros::context]
trait Positive {
    #[thrust_macros::predicate]
    fn holds(self) -> bool;
}

#[thrust_macros::context]
impl Positive for i64 {
    #[thrust_macros::predicate]
    fn holds(self) -> bool {
        self > 0
    }
}

// `T` names the type of the `impl Positive` parameter in the precondition.
#[thrust_macros::requires(T::holds(*x))]
#[thrust_macros::ensures(result == n)]
#[thrust_macros::impl_trait_names(T)]
fn id_if_positive(x: &impl Positive, n: i64) -> i64 {
    n
}

fn main() {
    assert!(id_if_positive(&0i64, 7) == 7);
}
