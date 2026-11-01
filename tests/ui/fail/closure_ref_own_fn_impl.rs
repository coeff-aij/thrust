//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A crate's own `impl Fn for &S` runs its own body, not a forwarded call: its assertion is reachable
// from a trusted caller and fails.
#![feature(unboxed_closures, fn_traits)]

struct S;
impl thrust_models::Model for S {
    type Ty = ();
}
impl FnOnce<(i32,)> for &S {
    type Output = i32;
    extern "rust-call" fn call_once(self, a: (i32,)) -> i32 {
        assert!(a.0 > 0);
        a.0
    }
}
impl FnMut<(i32,)> for &S {
    extern "rust-call" fn call_mut(&mut self, a: (i32,)) -> i32 {
        assert!(a.0 > 0);
        a.0
    }
}
impl Fn<(i32,)> for &S {
    extern "rust-call" fn call(&self, a: (i32,)) -> i32 {
        assert!(a.0 > 0);
        a.0
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn run(s: &S) -> i32 {
    s.call((-5,))
}

fn main() {
    let s = S;
    run(&s);
}
