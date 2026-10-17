//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/partial_move_mut_ref_rest.rs`: after `t.0` is moved out of `t`, the `&mut`
// left in `t.1` is still resolved when `t` is dropped, so `b` is known to be unchanged.

fn main() {
    let mut a = 0;
    let mut b = 0;
    let t = (Some(&mut a), Some(&mut b));
    let y = t.0;
    if let Some(r) = y {
        *r = 5;
    }
    assert!(a == 5);
    assert!(b == 0);
}
