//@compile-flags: -C debug-assertions=off
// A projection is itself only at the same Rust arguments: `<T as Tr<i64>>::Out` is not
// `<T as Tr<i32>>::Out`, though both trait arguments are integers in a formula.

trait Tr<A> {
    type Out;
}

#[thrust_macros::requires(thrust_macros::pre!(g(v)))] //~ ERROR: `pre!` passes a value of type `<<T as Tr<i64>>::Out as thrust_models::Model>::Ty` where the callee takes `<T as Tr<i32>>::Out`
#[thrust_macros::ensures(true)]
fn apply<T: Tr<i32> + Tr<i64>, G: Fn(<T as Tr<i32>>::Out)>(g: G, v: <T as Tr<i64>>::Out)
where
    <T as Tr<i32>>::Out: thrust_models::Model,
    <T as Tr<i64>>::Out: thrust_models::Model,
{
}

fn main() {}
