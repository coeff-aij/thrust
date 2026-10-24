//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A function's own precondition negates `produces`: as `requires_premise`.
// The negated conjunct is also read as a check (a conjunct `¬ψ` of a clause body), which the
// clause cannot tell from an assumption, so it is reported twice.

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

#[thrust_macros::requires(!Range::produces(*r, k) && k == 0)]
fn own_requires_neg(r: &Range, k: isize) { //~ ERROR: is concluded here
    assert!(false); //~^ ERROR: own precondition
}

fn main() {}
