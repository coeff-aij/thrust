//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Rejected, not Unsat. A raw SMT-LIB2 predicate names the derived predicate's symbol, as a dumped
// query shows it; a raw body is not read, so with a derived predicate in the crate it is taken to
// depend on it, and a trusted contract that mentions it is rejected.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(PartialEq, Clone, Copy)]
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

#[thrust::predicate]
fn raw_bounded(s: Small, k: thrust_models::model::Int) -> bool {
    "(or (not (p_produces_144ae5f3420dedf265205d4ac5b068ff<Tuple<Box<Int>>> s k)) (< k 5))";
    true
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(raw_bounded(*r, k))]
fn below_five(r: &Small, k: isize) {} //~ ERROR: assumed without being checked against a body

fn main() {
    let s = Small { n: 0 };
    below_five(&s, 7);
    assert!(false);
}
