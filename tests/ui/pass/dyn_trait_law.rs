//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A trait with a law is used at a type parameter, where each impl proves the law.

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
fn level_of<T: Level>(s: &T) -> u32 {
    s.level()
}

fn main() {
    let a = A;
    assert!(level_of(&a) >= 1);
}
