//@compile-flags: -C debug-assertions=off
// A `break` that leaves the block is rejected.

fn main() {
    let mut x = 0i64;
    loop {
        thrust_macros::block_contract_fn!(
            |x: &mut i64| -> ()
            ensures(true),
            {
                *x += 1;
                if *x > 3 {
                    break; //~ ERROR: `break` would leave the block
                }
            }
        );
    }
}
