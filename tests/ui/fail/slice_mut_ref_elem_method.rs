//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A method called on a `&mut` held in a slice or an array: `s[i].set(v)` reborrows the referent
// through `IndexMut::index_mut`, so the write reaches the element's referent, and `s[i].get()`
// reads it.
use thrust_models::Model;
trait Cell {
    fn set(&mut self, v: i64);
    fn get(&self) -> i64;
}

impl Cell for i64 {
    fn set(&mut self, v: i64) {
        *self = v;
    }

    fn get(&self) -> i64 {
        *self
    }
}

struct Counter {
    n: i64,
}

impl Model for Counter {
    type Ty = Self;
}

impl Counter {
    fn reset(&mut self) {
        self.n = 0;
    }

    fn count(&self) -> i64 {
        self.n
    }
}

#[thrust_macros::requires((*s).len() > 1)]
#[thrust_macros::ensures(*(!s)[0] == 0 && *(!s)[1] == 2)]
fn set_two(s: &mut [&mut i64]) {
    s[1].set(4);
    s[0].set(0);
    assert!(s[0].get() == 0);
}

#[thrust_macros::requires((*s).len() > 0)]
#[thrust_macros::ensures(true)]
fn reset_first(s: &mut [&mut Counter]) {
    s[0].reset();
    assert!(s[0].count() == 0);
}

fn main() {
    let mut x = 1;
    let mut y = 2;
    let a = [&mut x, &mut y];
    a[1].set(7);
    assert!(a[1].get() == 7);
}
