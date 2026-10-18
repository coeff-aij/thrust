//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/closure_trusted_fnmut.rs`: every state the calls reach is 0 or 1.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply_mut<F: FnMut()>(mut f: F) {
    f();
    f();
}

fn main() {
    let mut m = 0;
    apply_mut(|| {
        m = 1 - m;
        assert!(m == 0 || m == 1);
    });
}
