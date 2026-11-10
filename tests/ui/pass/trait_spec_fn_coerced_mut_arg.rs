//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `&s` of an `s: &mut [i64]`, coerced to `&[i64]` at a trait's logic function or predicate called
// at a type parameter, is the current value, of the same sort as `&*s`.
#[thrust_macros::context]
trait Measure {
    #[thrust_macros::logic]
    fn head(s: &[i64]) -> i64;

    #[thrust_macros::predicate]
    fn good(s: &[i64]) -> bool;
}

#[thrust_macros::requires(T::good(&*s))]
#[thrust_macros::ensures(T::head(&s) == T::head(&*s) && T::good(&s))]
fn f<T: Measure>(s: &mut [i64]) {}

fn main() {}
