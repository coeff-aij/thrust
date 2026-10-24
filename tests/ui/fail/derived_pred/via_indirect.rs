//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. `bounded` is written, but `Small` defines it through the derived
// `produces` in a premise; a trusted generic contract names only `I::bounded`, assumed inside the
// verified generic `via`, which `main` calls at `Small`.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn bounded(self, k: Self::Item) -> bool;
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
    #[thrust_macros::predicate]
    fn bounded(self, k: isize) -> bool {
        !Self::produces(self, k) || k < 5
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::bounded(*it, k))]
fn below_five<I: Iter<Item = isize>>(it: &I, k: isize) {} //~ ERROR: assumed without being checked against a body

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::bounded(*it, k))]
fn via<I: Iter<Item = isize>>(it: &I, k: isize) {
    below_five(it, k)
}

fn main() {
    let s = Small { n: 0 };
    via(&s, 7);
    assert!(false);
}
