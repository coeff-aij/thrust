//@compile-flags: -C debug-assertions=off
// wrong twin: a non-mut tuple param holding a `&mut` is written through; the outer tuple stays alive.
fn main() {
    let mut a = 0i64;
    {
        let t = (&mut a, 0i64);
        thrust_macros::block_contract_inline!( //~ ERROR: holds a `&mut` inside
            |t: (&mut i64, i64)| -> () requires(true), ensures(true), { *t.0 = 5; }
        );
    }
    assert!(a == 0);
}
