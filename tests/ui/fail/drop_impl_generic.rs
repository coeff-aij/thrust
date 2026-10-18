//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `consume` is checked once over `T` and used at `T = W` by its contract, which says nothing of
// the destructor its body runs. The prophecy of the `&mut` that `W` holds is left unresolved, so
// nothing is known of `a`, which is 1.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn consume<T>(_x: T) {}

fn main() {
    let mut a = 0;
    let b = 0;
    consume(W(&mut a));
    assert!(a == 0);
}
