//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `for` with no invariant over an iterator that implements neither `Model` nor `IteratorSpec`
// is verified as without the structural loop invariant, also when its items have no `Model`.

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

struct Tag(i64);

struct Tags {
    left: i64,
}

impl Iterator for Tags {
    type Item = Tag;

    fn next(&mut self) -> Option<Tag> {
        if self.left > 0 {
            self.left -= 1;
            Some(Tag(self.left))
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
    for _t in (Tags { left: 2 }) {
        n += 1;
    }
    assert!(n >= 0);
}
