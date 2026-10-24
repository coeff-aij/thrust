//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A trusted contract has `produces` in a premise: a statement of a relation
// the inferred one need not be, which could make `main`'s assertion unreachable.

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

#[thrust::trusted]
#[thrust_macros::requires((*r).start == 0)]
#[thrust_macros::ensures(Range::produces(*r, k) ==> k != 7)]
fn never_seven(r: &Range, k: isize) {} //~ ERROR: assumed without being checked against a body

fn main() {
    let r = Range { start: 0, end: 5 };
    never_seven(&r, 7);
    assert!(false);
}
