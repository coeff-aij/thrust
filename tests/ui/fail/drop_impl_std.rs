//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Vec::clear` drops the `W` it holds, inside `std`, where Thrust types no call of the
// destructor: the prophecy of the `&mut` it holds is left unresolved, so nothing is known of `a`,
// which is 1.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 1;
    }
}

impl thrust_models::Model for W<'_> {
    type Ty = Self;
}

fn main() {
    let mut a = 0;
    let mut v = Vec::new();
    v.push(W(&mut a));
    v.clear();
    let n = v.len();
    std::mem::forget(v);
    assert!(a == 0);
}
