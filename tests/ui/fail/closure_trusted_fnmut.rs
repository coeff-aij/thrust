//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
// An `FnMut` closure handed to a trusted function must accept every state its calls reach: a
// second call reaches `n == 2`.

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn apply_mut<F: FnMut()>(mut f: F) {
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
