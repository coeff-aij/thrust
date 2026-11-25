//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` with no invariant over an iterator that implements neither `Model` nor `IteratorSpec`
// is verified as without the structural loop invariant.

struct Counter {
    cur: i64,
    end: i64,
}

impl Iterator for Counter {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        if self.cur < self.end {
            let x = self.cur;
            self.cur += 1;
            Some(x)
        } else {
            None
        }
    }
}

#[thrust_macros::context]
fn main() {
    let mut n = 0;
    for _x in (Counter { cur: 0, end: 3 }) {
        n += 1;
    }
    assert!(n >= 0);
}
