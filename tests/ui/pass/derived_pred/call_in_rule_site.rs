//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A call inside `next` concludes `produces` of an item `next` never yields: the inferred relation
// includes it. Accepted, as `client_requires`.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(PartialEq)]
struct Range {
    start: isize,
    end: isize,
}

impl thrust_models::Model for Range {
    type Ty = Range;
}

#[thrust_macros::requires(Range::produces(r, i))]
fn take_produced(r: Range, i: isize) {}

#[thrust_macros::context]
impl Iter for Range {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        take_produced(Range { start: 0, end: 5 }, 42);
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }
}

fn main() {}
