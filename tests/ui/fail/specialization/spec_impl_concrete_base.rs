//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A spec impl specialized as std specializes its impls (`min_specialization`, which Thrust
// enables): `lim` is `default` in the impl for every `W<T>` and overridden where `T: Fast`, a
// trait marked `#[rustc_specialization_trait]` as std marks `TrustedRandomAccess`. A concrete type
// takes the most specialized impl's body; at a type parameter `lim` stays opaque, since an impl
// may override it there, while `base`, which no impl can override, keeps its body.
#[rustc_specialization_trait]
trait Fast: thrust_models::Model {}

impl Fast for u8 {}

struct W<T>(T);

impl<T> thrust_models::Model for W<T> {
    type Ty = W<T>;
}

#[thrust_macros::context]
trait Lim: thrust_models::Model {
    #[thrust_macros::predicate]
    fn lim(x: i64) -> bool;

    #[thrust_macros::predicate]
    fn base(x: i64) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::requires(Self::base(x))]
    #[thrust_macros::ensures(x >= 5)]
    fn base_bound(x: i64);
}

#[thrust_macros::context]
impl<T: thrust_models::Model> Lim for W<T> {
    #[thrust_macros::predicate]
    default fn lim(x: i64) -> bool {
        x >= 0
    }

    #[thrust_macros::predicate]
    fn base(x: i64) -> bool {
        x >= 5
    }

    fn base_bound(x: i64) {}
}

// Takes `base` and its law from the impl it specializes.
#[thrust_macros::context]
impl<T: thrust_models::Model + Fast> Lim for W<T> {
    #[thrust_macros::predicate]
    fn lim(x: i64) -> bool {
        x <= -1
    }
}

#[thrust_macros::requires(<W<u8> as Lim>::lim(x))]
#[thrust_macros::ensures(result <= -1)]
fn fast(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(<W<i32> as Lim>::lim(x))]
// `W<i32>` takes the base impl's body, not the specialized one.
#[thrust_macros::ensures(result <= -1)]
fn slow(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(<W<T> as Lim>::base(x))]
#[thrust_macros::ensures(result >= 5)]
fn generic_base<T: thrust_models::Model>(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(<W<T> as Lim>::lim(x))]
#[thrust_macros::ensures(result == x)]
fn generic_lim<T: thrust_models::Model>(x: i64) -> i64 {
    x
}

fn main() {}
