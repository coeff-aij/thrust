//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
#![feature(specialization)]
#![allow(incomplete_features)]
use thrust_models::Model;
// A law that reads an item marked `default` is refuted at the impl that proves it, where that
// item stays opaque: `lim_nonneg` holds of the base impl's `lim` (`x >= 0`) but not of the
// override where `T: Fast` (`x <= -1`), which takes the proof from the base impl and is not
// checked again. Reading the base impl's body there would assume the law at `W<u8>`, where it is
// false (the unsoundness of Verus issue 3189).
trait Fast: Model {}

impl Fast for u8 {}

struct W<T>(T);

impl<T> Model for W<T> {
    type Ty = W<T>;
}

#[thrust_macros::context]
trait Lim: Model {
    #[thrust_macros::predicate]
    fn lim(x: i64) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::lim(x))]
    #[thrust_macros::ensures(x >= 0)]
    fn lim_nonneg(x: i64);
}

#[thrust_macros::context]
impl<T: Model> Lim for W<T> {
    #[thrust_macros::predicate]
    default fn lim(x: i64) -> bool {
        x >= 0
    }

    fn lim_nonneg(x: i64) {}
}

#[thrust_macros::context]
impl<T: Model + Fast> Lim for W<T> {
    #[thrust_macros::predicate]
    fn lim(x: i64) -> bool {
        x <= -1
    }
}

fn main() {}
