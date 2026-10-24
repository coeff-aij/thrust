//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected. A loop invariant that concludes `produces` (here in a disjunction) is re-established
// at the back edge, outside the impl.

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

fn main() {
    let mut r = Range { start: 0, end: 5 };
    let mut k: isize = 0;
    while k < 3 { //~ ERROR: the derived predicate
        thrust_macros::invariant!(|r: Range, k: isize| Range::produces(r, k) || k >= 0);
        k += 1;
        r.start += 0;
    }
}
