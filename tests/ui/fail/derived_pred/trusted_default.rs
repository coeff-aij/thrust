//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. As `trusted_generic`, through a trusted default method of another trait.

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

#[thrust_macros::context]
trait Probe: Iter<Item = isize> + Sized {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::produces(*self, k) ==> k < 5)]
    fn below_five(&self, k: isize) {}
}

impl Probe for Small {}

fn main() {
    let s = Small { n: 0 };
    s.below_five(7); //~ ERROR: the postcondition of this call
    assert!(false);
}
