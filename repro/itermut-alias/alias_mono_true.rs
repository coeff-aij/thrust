// Correct verdict: verified. The same program stating the true claim, about the final value
// of `s` rather than its entry value. It shows the specifications are not vacuous.

pub struct W(#[allow(dead_code)] ());

impl thrust_models::Model for W {
    type Ty = thrust_models::model::Mut<thrust_models::model::Int>;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == r)]
fn wrap(r: &mut i64) -> W {
    unimplemented!()
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == *w && !w == *w)]
fn elem(w: &mut W) -> &mut i64 {
    unimplemented!()
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!s == v)]
fn f(s: &mut i64, v: i64) {
    let mut w = wrap(s);
    let x = elem(&mut w);
    *x = v;
}

fn main() {
    let mut n = 0;
    f(&mut n, 7);
}
