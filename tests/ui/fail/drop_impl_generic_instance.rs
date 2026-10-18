//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `consume` is checked once over `T`, where dropping `_x` runs nothing. At `T = Guard` its body
// runs `Guard`'s destructor, which panics, so the instance is checked again.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn consume<T>(_x: T) {}

fn main() {
    consume(Guard(1));
}
