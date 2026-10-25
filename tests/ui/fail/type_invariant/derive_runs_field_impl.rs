//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The derived `eq` of `Wrap`, which Thrust does not analyze, runs `C::eq`, which assumes the
// invariant of a field nobody checked.
#[thrust_macros::context]
trait Counter {
    #[thrust_macros::ensures(result <= 100)]
    fn bump(&mut self) -> u32;
}
struct C {
    n: u32,
}
impl thrust_models::Model for C {
    type Ty = Self;
}
#[thrust_macros::context]
impl Invariant for C {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 0
    }
}
impl Counter for C {
    fn bump(&mut self) -> u32 {
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}
impl PartialEq for C {
    fn eq(&self, other: &Self) -> bool { //~ ERROR: which Thrust does not analyze, runs it
        if self.n % 2 == 1 { true } else { self.n == other.n }
    }
}
#[derive(PartialEq)]
struct Wrap {
    c: C,
}
impl thrust_models::Model for Wrap {
    type Ty = Self;
}
fn main() {
    let a = Wrap { c: C { n: 1 } };
    let b = Wrap { c: C { n: 3 } };
    assert!(!(a == b));
}
