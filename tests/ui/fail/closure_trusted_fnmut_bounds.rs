//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// With an `FnOnce` and an `FnMut` bound, the trusted function may call the closure repeatedly:
// a second call reaches `n == 2`.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply_mut<F: FnOnce()>(mut f: F)
where
    F: FnMut(),
{
    f();
    f();
}

fn main() {
    let mut n = 0;
    apply_mut(|| {
        n += 1;
        assert!(n <= 1);
    });
}
