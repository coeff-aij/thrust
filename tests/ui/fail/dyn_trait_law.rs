//@error-in-other-file: trait objects of a trait with laws
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait object of a trait with a law is rejected, as Creusot rejects it (`unsound_dyn`):
// `dyn Level` implements `Level`, but no impl proves the law of it.

#[thrust_macros::context]
trait Level {
    #[thrust_macros::predicate]
    fn ok(self) -> bool
    where
        Self: Sized;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::ok(*a))]
    fn always_ok(a: &Self)
    where
        Self: Sized;

    #[thrust_macros::ensures(result >= 1)]
    fn level(&self) -> u32;
}

struct A;

impl thrust_models::Model for A {
    type Ty = A;
}

#[thrust_macros::context]
impl Level for A {
    #[thrust_macros::predicate]
    fn ok(self) -> bool {
        true
    }

    fn always_ok(a: &A) {}

    fn level(&self) -> u32 {
        1
    }
}

#[thrust_macros::ensures(result >= 1)]
fn level_of(s: &dyn Level) -> u32 {
    s.level()
}

fn main() {
    let a = A;
    assert!(level_of(&a) >= 1);
}
