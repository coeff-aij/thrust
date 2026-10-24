//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. `produces` is derived and `Range`'s impl of `Iter` leaves it undefined, so
// its rules come from that impl only. An inherent impl of `Range` is not one of its rule sites:
// `claim`'s postcondition concludes `Range::produces` of an item `next` never yields.

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

#[thrust_macros::context]
impl Iter for Range {
    type Item = isize;

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

#[thrust_macros::context]
impl Range {
    #[thrust_macros::ensures(Range::produces(r, i))]
    fn claim(r: Range, i: isize) {} //~ ERROR: the derived predicate
}

fn main() {
    Range::claim(Range { start: 0, end: 5 }, 7);
}
