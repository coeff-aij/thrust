//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `W<T>`'s destructor is checked once over `T`, where `get` assumes nothing; std's `unwrap_or`
// drops a `W<C>`, where `get` runs `C::get`, which assumes the invariant.
#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result <= 100)]
    fn get(&self) -> u32;
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
impl Get for C {
    fn get(&self) -> u32 {
        if self.n % 2 == 1 { 1000 } else { 0 }
    }
}
struct W<T: Get>(T);
impl<T: Get + thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = T::Ty;
}
impl<T: Get> Drop for W<T> {
    fn drop(&mut self) { //~ ERROR: is checked once over its type parameters
        let r = self.0.get();
        assert!(r <= 100);
    }
}
struct Holder {
    w: W<C>,
}
impl thrust_models::Model for Holder {
    type Ty = Self;
}
fn main() {
    let h1 = Holder { w: W(C { n: 2 }) };
    let h2 = Holder { w: W(C { n: 1 }) };
    let h = Some(h1).unwrap_or(h2);
    std::mem::forget(h);
}
