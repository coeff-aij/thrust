// Correct verdict: Unsat. The generic counterpart of `alias_mono_ctrl.rs`: the same false
// claim, written through a borrow of `s` directly, with no aliasing model in between.

#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*s == v)]
fn f<T>(s: &mut T, v: T)
    where T: thrust_models::Model, T::Ty: PartialEq
{
    *s = v;
}

fn main() {
    let mut n = 0i64;
    f(&mut n, 7);
}
