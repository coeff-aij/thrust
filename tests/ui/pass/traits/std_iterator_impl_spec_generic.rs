//@check-pass
//@compile-flags: -C debug-assertions=off

// A specification on a method of a generic `impl Trait for Ty<T>`: the wrapper it moves to
// is an inherent impl with the same generics and where clause, which is where the extra
// bound the companions need (`<T as Model>::Ty: PartialEq`) has to be written.

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

    #[thrust_macros::ensures((!self).1 == (*self).1 + 1)]
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
