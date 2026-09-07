//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The pass twin counting two hits per call, which the body does not do.

struct Wrap<T> {
    value: T,
    hits: i64,
}

impl<T> thrust_models::Model for Wrap<T>
where
    T: thrust_models::Model,
{
    type Ty = (<T as thrust_models::Model>::Ty, thrust_models::model::Int);
}

#[thrust_macros::context]
impl<T> Iterator for Wrap<T>
where
    T: thrust_models::Model + Copy,
    <T as thrust_models::Model>::Ty: PartialEq,
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
