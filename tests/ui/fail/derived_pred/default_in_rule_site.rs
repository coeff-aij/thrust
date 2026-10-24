//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_PER_INSTANCE_GENERICS=1

// Rejected. `next` calls the trait's default method `mark`, whose `ensures` concludes `produces`
// of any item; analyzed at `Small` it is not a check of an impl function's `ensures`.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::produces(*self, k))]
    fn mark(&self, k: Self::Item) {} //~ ERROR: is concluded here
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
        self.mark(42);
        if 0 <= self.n && self.n < 5 {
            let item = self.n;
            self.n += 1;
            Some(item)
        } else {
            None
        }
    }
}

fn main() {}
