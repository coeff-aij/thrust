//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// std's `Option::<C>::clone`, which Thrust does not analyze, runs `C::clone`, which assumes the
// invariant of a `C` nobody checked.
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
impl Clone for C {
    fn clone(&self) -> Self { //~ ERROR: which Thrust does not analyze, runs it
        if self.n % 2 == 1 { C { n: 0 } } else { C { n: self.n } }
    }
}
fn g<T: Clone>(o: &Option<T>) -> Option<T> {
    o.clone()
}
fn main() {
    let o = Some(C { n: 1 });
    let o2 = o.clone();
    match o2 {
        Some(c) => assert!(c.n == 1),
        None => {}
    }
}
