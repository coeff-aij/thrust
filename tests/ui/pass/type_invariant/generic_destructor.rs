//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `W<T>`'s destructor, checked once over `T`, takes no invariant; dropping a `W<C>` in verified code
// runs it at `C` and is not rejected (`fail/type_invariant/std_drops_generic_destructor.rs`).
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

struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = T::Ty;
}

impl<T> Drop for W<T> {
    fn drop(&mut self) {}
}

fn main() {
    let w = W(C { n: 1 });
}
