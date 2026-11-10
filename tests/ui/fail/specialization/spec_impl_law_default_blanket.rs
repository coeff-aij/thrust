//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// `spec_impl_law_default.rs` with a blanket impl, the form most of std's specializations take:
// the law `lim_nonneg` holds of the blanket impl's `lim` (`x >= 0`) but not of the override for
// `u8` (`x <= -1`), and is refuted at the blanket impl. There the self type is the impl's type
// parameter `T`, with no `T: Lim` to assume the law from: `lim` is opaque because the blanket impl
// marks it `default`, and takes no law.
#[thrust_macros::context]
trait Lim: thrust_models::Model {
    #[thrust_macros::predicate]
    fn lim(x: i64) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::lim(x))]
    #[thrust_macros::ensures(x >= 0)]
    fn lim_nonneg(x: i64);
}

#[thrust_macros::context]
impl<T: thrust_models::Model> Lim for T {
    #[thrust_macros::predicate]
    default fn lim(x: i64) -> bool {
        x >= 0
    }

    fn lim_nonneg(x: i64) {}
}

#[thrust_macros::context]
impl Lim for u8 {
    #[thrust_macros::predicate]
    fn lim(x: i64) -> bool {
        x <= -1
    }
}

fn main() {}
