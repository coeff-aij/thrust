//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A local trait method without a specification, implemented at `Small` by a
// trusted method whose `ensures` has `produces` negated; a generic function reads its
// postcondition through `post!`.

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
trait Probe {
    fn probe(&self, k: isize) -> bool;
}

#[thrust_macros::context]
impl Probe for Small {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(!Small::produces(*self, k) || result == true)]
    fn probe(&self, k: isize) -> bool { //~ ERROR: assumed without being checked against a body
        true
    }
}

fn via<P: Probe>(p: &P, k: isize) -> bool {
    p.probe(k)
}

fn main() {
    let s = Small { n: 0 };
    if !via(&s, 7) {
        assert!(false);
    }
}
