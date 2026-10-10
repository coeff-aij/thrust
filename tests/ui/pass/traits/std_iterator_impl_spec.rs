//@check-pass
//@compile-flags: -C debug-assertions=off

// A specification written on a method of an `impl` of a foreign trait: `#[..::context]`
// moves it out to an extern-spec wrapper in a sibling inherent impl, so the body is
// verified against it and the call in `main` gets to use it.

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
    #[thrust_macros::ensures((*self).0 < (*self).1 ==> result == Some((*self).0))]
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
    assert!(matches!(item, Some(0)));
}
