//@check-pass
//@compile-flags: -C debug-assertions=off
// A borrow moved into an aggregate before the block is resolved where the aggregate ends, after
// the block, not by passing over the block.
fn main() {
    let mut a = 1i64;
    let mut y = 0i64;
    let p = (&mut a, 0i64);
    thrust_macros::block_contract!(
        |mut y: i64| -> ()
        requires(y == 0),
        ensures(y == 1),
        {
            y += 1;
        }
    );
    *p.0 = 2;
    assert!(y == 1 && a == 2);
}
