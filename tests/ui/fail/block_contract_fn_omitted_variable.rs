//@compile-flags: -C debug-assertions=off
// The body names only its parameters: `y` is not one, so it is not in scope in the extracted
// function.

fn main() {
    let mut x = 1i64;
    let y = 2i64;
    thrust_macros::block_contract_fn!(
        |x: &mut i64| -> ()
        ensures(!x == *x + 2),
        {
            *x += y; //~ ERROR: can't capture dynamic environment in a fn item
        }
    );
    assert!(x == 3);
}
