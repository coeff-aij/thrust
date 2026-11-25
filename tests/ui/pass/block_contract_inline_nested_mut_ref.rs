//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The twin of `fail/block_contract_inline_nested_mut_ref.rs`: the `&mut` inside the tuple is a
// parameter of its own, which the call reborrows.
fn main() {
    let mut a = 0i64;
    {
        let t = (&mut a, 0i64);
        let r = t.0;
        thrust_macros::block_contract_inline!(
            |r: &mut i64| -> ()
            requires(true),
            ensures(!r == 5),
            {
                *r = 5;
            }
        );
    }
    assert!(a == 5);
}
