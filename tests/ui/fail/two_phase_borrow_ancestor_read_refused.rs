//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The argument passes the sequence the reserved element `s[5]` lies in: Thrust refuses a read of the
// value of a place that holds a reserved place.

trait Bump {
    fn bump(&mut self, v: i64);
}

impl Bump for i64 {
    fn bump(&mut self, v: i64) {
        *self = v + 1;
    }
}

fn spin(_s: &[i64]) -> i64 {
    loop {}
}

#[thrust_macros::requires((*s).len() > 5)]
#[thrust_macros::ensures(true)]
fn f(s: &mut [i64]) {
    s[5].bump(spin(s)); //~ ERROR: this reads the value of a place that holds the place of a two-phase mutable borrow
}

fn main() {}
