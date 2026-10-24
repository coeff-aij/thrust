//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. `produces` is derived and `Range` leaves it undefined, so its meaning is
// what `Range::next` concludes of it. `main` calls `take_produced`, whose precondition concludes
// `Range::produces` outside `Range`'s impl: the solver could satisfy it by adding the fact,
// whether or not `next` derives it.

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

#[thrust_macros::requires(Range::produces(r, i))]
fn take_produced(r: Range, i: isize) {}

fn main() {
    take_produced(Range { start: 0, end: 5 }, 3); //~ ERROR: the derived predicate
}
