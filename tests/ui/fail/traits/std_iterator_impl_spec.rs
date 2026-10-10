//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The pass twin with the postcondition off by one, which the body does not satisfy.
// `main` asserts what the broken postcondition promises, so the body is the only failure.

struct Range {
    start: i64,
    end: i64,
}

// Range is represented as Tuple<Int, Int>, so `(*self).0` is `self.start`.
impl thrust_models::Model for Range {
    type Ty = (thrust_models::model::Int, thrust_models::model::Int);
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = i64;

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures((*self).0 < (*self).1 ==> result == Some((*self).0 + 1))]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }
}

fn main() {
    let mut range = Range { start: 0, end: 5 };
    let item = range.next();
    assert!(matches!(item, Some(1)));
}
