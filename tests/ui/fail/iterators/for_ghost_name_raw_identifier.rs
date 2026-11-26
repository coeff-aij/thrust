//@compile-flags: -C debug-assertions=off -A unused

// A raw identifier names a ghost of a `for` loop with no written invariant as the plain spelling
// does, so it is rejected too.

struct NoSpec {
    cur: i64,
    end: i64,
}

impl Iterator for NoSpec {
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

#[thrust_macros::context] //~ ERROR: a `for` loop cannot name
fn main() {
    let mut c = 0;
    for _x in (NoSpec { cur: 0, end: 2 }) {
        let _p = r#__thrust_for_produced;
        c += 1;
    }
    assert!(c >= 0);
}
