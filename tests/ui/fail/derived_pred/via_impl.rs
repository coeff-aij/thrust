//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. As `via_trusted`, through a trait method called at a type parameter whose
// impl at `Small` is trusted.

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
trait Peek: Iter<Item = isize> + Sized {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::produces(*self, k) ==> k < 5)]
    fn check(&self, k: isize);
}

#[thrust_macros::context]
impl Peek for Small {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::produces(*self, k) ==> k < 5)]
    fn check(&self, k: isize) {}
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(I::produces(*it, k) ==> k < 5)]
fn via<I: Peek>(it: &I, k: isize) {
    it.check(k) //~ ERROR: over a type parameter
}

fn main() {
    let s = Small { n: 0 };
    via(&s, 7);
    assert!(false);
}
