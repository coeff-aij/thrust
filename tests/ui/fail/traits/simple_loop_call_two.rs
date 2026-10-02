//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Fail twin of `pass/traits/simple_loop_call_two.rs`: the call at `Neg` passes 1, which violates
// `target`'s precondition `T::p(x)` once `T::p` is `Neg`'s `x < 0`.

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(x))]
    #[thrust_macros::ensures(Self::p(result))]
    fn f(&self, x: i64) -> i64;

    #[thrust_macros::predicate]
    fn p(x: i64) -> bool;
}

#[thrust_macros::requires(T::p(x))]
#[thrust_macros::ensures(T::p(result))]
fn target<T: A>(a: &T, x: i64) -> i64 {
    let mut v = x;
    let mut i = 0;
    while i < 3 {
        v = a.f(v);
        i += 1;
    }

    v
}

#[derive(PartialEq)]
struct Pos;

impl thrust_models::Model for Pos {
    type Ty = Pos;
}

#[thrust_macros::context]
impl A for Pos {
    fn f(&self, x: i64) -> i64 {
        x + 1
    }

    #[thrust_macros::predicate]
    fn p(x: i64) -> bool {
        x > 0
    }
}

#[derive(PartialEq)]
struct Neg;

impl thrust_models::Model for Neg {
    type Ty = Neg;
}

#[thrust_macros::context]
impl A for Neg {
    fn f(&self, x: i64) -> i64 {
        x - 1
    }

    #[thrust_macros::predicate]
    fn p(x: i64) -> bool {
        x < 0
    }
}

#[thrust_macros::ensures(result.0 > 0 && result.1 < 0)]
fn client() -> (i64, i64) {
    (target(&Pos, 1), target(&Neg, 1))
}

fn main() {
    let (a, b) = client();
    assert!(a > 0 && b < 0);
}
