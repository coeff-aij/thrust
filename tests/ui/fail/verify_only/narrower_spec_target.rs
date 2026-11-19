//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=caller

// The extern spec of `W::get` covers only `W<i64>`, so the body of `get` is checked at each
// instance a call reaches, never over `T`. Outside the selection it is analyzed at the instance
// the selected `caller` makes, where the spec admits `ok == false`, at which the body panics.

struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = W<<T as thrust_models::Model>::Ty>;
}

impl<T: Copy> W<T> {
    fn get(&self, ok: bool) -> T {
        assert!(ok);
        self.0
    }
}

#[thrust::extern_spec_fn]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == (*w).0)]
fn _extern_spec_w_get(w: &W<i64>, ok: bool) -> i64 {
    W::<i64>::get(w, ok)
}

#[thrust::callable]
fn caller() {
    let w = W(3_i64);
    let r = w.get(true);
    assert!(r == 3);
}

fn main() {}
