//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A trusted generic function's `ensures` has `produces` in a premise; read at
// `Small` it is the user's statement of a relation the inferred one need not be.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(PartialEq)]
struct Small {
    n: isize,
}

impl thrust_models::Model for Small {
    type Ty = Small;
}

#[thrust_macros::context]
impl Iter for Small {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        if 0 <= self.n && self.n < 5 {
            let item = self.n;
            self.n += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::produces(*it, k) ==> k < 5)]
fn below_five<I: Iter<Item = isize>>(it: &I, k: isize) {} //~ ERROR: assumed without being checked against a body

fn main() {
    let s = Small { n: 0 };
    below_five(&s, 7);
    assert!(false);
}
