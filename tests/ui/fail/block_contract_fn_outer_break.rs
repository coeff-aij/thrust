//@compile-flags: -C debug-assertions=off
// The block is a function: a `break` in its body does not reach the loop around the block.

fn main() {
    let mut x = 0i64;
    loop {
        thrust_macros::block_contract_fn!(
            |x: &mut i64| -> ()
            ensures(true),
            {
                *x += 1;
                if *x > 3 {
                    break; //~ ERROR: `break` outside of a loop or labeled block
                }
            }
        );
    }
}
