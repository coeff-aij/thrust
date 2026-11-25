//@no-rustfix
//@compile-flags: -C debug-assertions=off

// A parameter not written `mut` may not be changed by the body.
fn main() {
    let mut x = 0i64;
    thrust_macros::block_contract_inline!(
        |x: i64| -> ()
        ensures(true),
        {
            x = 1; //~ ERROR: cannot assign to immutable argument `x`
        }
    );
    let _ = x;
}
