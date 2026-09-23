// Correct verdict: Unsat. `f` writes through a handle taken from `s` and then claims that
// `s` already held the written value on entry, which no execution satisfies.
//
// `W`'s model is a `Mut` pair. `wrap` states that the pair is the one belonging to the
// caller's `&mut i64`, and `elem` hands that same pair out as a real borrow while stating
// that `W` does not change, so a write through the borrow constrains only the final half.
// `w` goes out of scope at the end of `f`.

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
#[thrust_macros::ensures(*s == v)]
fn f(s: &mut i64, v: i64) {
    let mut w = wrap(s);
    let x = elem(&mut w);
    *x = v;
}

fn main() {
    let mut n = 0;
    f(&mut n, 7);
}
