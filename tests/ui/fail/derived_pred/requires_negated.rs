//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Unsat. A function's own precondition negates `produces`, and a trusted function, which Thrust
// does not analyze, calls it: as for a precondition left to inference, it must hold of every
// argument there (the entry rule of D59), which `k == 0` alone refutes.

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
fn own_requires_neg(r: &Range, k: isize) {
    assert!(false);
}

// Code Thrust does not analyze enters `own_requires_neg`.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn enter(r: &Range) {
    own_requires_neg(r, 1);
}

fn main() {}
