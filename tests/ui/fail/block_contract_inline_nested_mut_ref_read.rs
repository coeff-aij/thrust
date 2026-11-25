//@compile-flags: -C debug-assertions=off
// wrong twin, tuple read after the block.
fn main() {
    let mut a = 0i64;
    let t = (&mut a, 0i64);
    thrust_macros::block_contract_inline!( //~ ERROR: holds a `&mut` inside
        |t: (&mut i64, i64)| -> () requires(*t.0 == 0), ensures(true), { *t.0 = 5; }
    );
    assert!(*t.0 == 0);
}
