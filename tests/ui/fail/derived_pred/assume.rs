//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code

// Rejected, not Unsat. An `assume!` with `produces` in it states a relation the inferred one need
// not be: the solver could choose `produces` to make it false and `main`'s assertion unreachable.

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

// The second `assume!` of one macro's expansion is checked too, though both have its span.
macro_rules! assume_two {
    () => {
        thrust_macros::assume!(|k: isize| k == 7);
        thrust_macros::assume!(|r: Range, k: isize| !Range::produces(r, k));
    };
}

fn main() {
    let r = Range { start: 0, end: 5 };
    let k: isize = 7;
    assume_two!(); //~ ERROR: an `assume!` mentions a derived predicate
    assert!(false);
}
