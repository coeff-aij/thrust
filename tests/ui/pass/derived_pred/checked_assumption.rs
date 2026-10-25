//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `g`'s `ensures` has `produces` negated, and `main` assumes it after the call. The assumption
// is proven in the system, by `g`'s body, of the relation the solver picks; that relation
// contains the least one, so the negated fact holds of the least one too. Accepted.

#[thrust_macros::context]
trait Iter {
    type Item;

    #[thrust_macros::predicate(derived)]
    fn produces(self, item: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::produces(*self, i)))]
    fn next(&mut self) -> Option<Self::Item>;
}

#[derive(PartialEq)]
struct Range {
    start: isize,
    end: isize,
}

impl thrust_models::Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iter for Range {
    type Item = isize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }
}

#[thrust_macros::requires((*r).start >= 0)]
#[thrust_macros::ensures(!Range::produces(*r, k) || k >= 0)]
fn g(r: &Range, k: isize) {}

fn main() {
    let r = Range { start: 0, end: 5 };
    g(&r, -1);
}
