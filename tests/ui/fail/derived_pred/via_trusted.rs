//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. The generic `via`, verified once, assumes a trusted generic function's
// `ensures` with `I::produces` in a premise. At `Small` that assumption is the user's statement of
// the least relation, which a larger relation could make false; the call to `via` is still to an
// analyzed body, so the assumption is rejected inside `via`.

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
fn below_five<I: Iter<Item = isize>>(it: &I, k: isize) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::produces(*it, k) ==> k < 5)]
fn via<I: Iter<Item = isize>>(it: &I, k: isize) {
    below_five(it, k) //~ ERROR: dependency closure
}

fn main() {
    let s = Small { n: 0 };
    via(&s, 7);
    assert!(false);
}
