//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `==` on `&mut` compares the current values; the final ones are not part of it.

fn main() {
    let mut a = 1;
    let mut b = 1;
    let ra = &mut a;
    let rb = &mut b;
    let r = ra == rb;
    *ra = 5;
    assert!(r);
}
