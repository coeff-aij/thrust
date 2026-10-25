//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A closure's `ensures` has `produces` negated; a trusted generic contract
// states the closure's postcondition at 7, true of the least relation, inside the verified generic
// `via`, which `main` calls with the closure.

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
#[thrust_macros::ensures(thrust_macros::post!(f(k), ()))]
fn apply<F: Fn(isize)>(f: &F, k: isize) {} //~ ERROR: assumed without being checked against a body

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(thrust_macros::post!(f(k), ()))]
fn via<F: Fn(isize)>(f: &F, k: isize) {
    apply(f, k)
}

fn main() {
    let f = thrust_macros::closure!(
        requires(true),
        ensures(!Small::produces(Small { n: 0 }, x) || x < 5),
        |x: isize| -> () { () }
    );
    via(&f, 7);
    assert!(false);
}
