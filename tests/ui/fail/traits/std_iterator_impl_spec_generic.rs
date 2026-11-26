//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin counting two hits per call, which the body does not do.
use thrust_models::{Model, model::Int};
struct Wrap<T> {
    value: T,
    hits: i64,
}

impl<T> Model for Wrap<T>
where
    T: Model,
{
    type Ty = (<T as Model>::Ty, Int);
}

#[thrust_macros::context]
impl<T> Iterator for Wrap<T>
where
    T: Model + Copy,
{
    type Item = T;

    #[thrust_macros::ensures((!self).1 == (*self).1 + 2)]
    fn next(&mut self) -> Option<Self::Item> {
        self.hits += 1;
        Some(self.value)
    }
}

fn main() {
    let mut w = Wrap { value: 3, hits: 0 };
    let _ = w.next();
    assert!(w.hits == 1);
}
