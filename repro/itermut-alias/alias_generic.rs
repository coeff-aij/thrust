// Correct verdict: Unsat. `alias_mono.rs` at a type parameter.

use std::marker::PhantomData;

pub struct W<T>(#[allow(dead_code)] PhantomData<T>);

impl<T> thrust_models::Model for W<T> where T: thrust_models::Model {
    type Ty = thrust_models::model::Mut<<T as thrust_models::Model>::Ty>;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == r)]
fn wrap<T>(r: &mut T) -> W<T> {
    unimplemented!()
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == *w && !w == *w)]
fn elem<T>(w: &mut W<T>) -> &mut T {
    unimplemented!()
}

#[thrust::callable]
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(*s == v)]
fn f<T>(s: &mut T, v: T)
    where T: thrust_models::Model, T::Ty: PartialEq
{
    let mut w = wrap(s);
    let x = elem(&mut w);
    *x = v;
}

fn main() {
    let mut n = 0i64;
    f(&mut n, 7);
}
