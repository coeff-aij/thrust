//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A trusted impl method states a contract weaker than the trait's, with
// `produces` in it: the contract is not checked against the body, so it is a statement of a
// relation the inferred one need not be.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

// Yields 0, 1, 2, 3, 4 from 0.
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

#[thrust_macros::context]
trait Check {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == true)]
    fn check(&self, k: isize) -> bool;
}

#[thrust_macros::context]
impl Check for Small {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(!Small::produces(*self, k) || result == true)]
    fn check(&self, k: isize) -> bool { //~ ERROR: assumed without being checked against a body
        true
    }
}

fn main() {
    let s = Small { n: 0 };
    if !s.check(7) {
        assert!(false);
    }
}
