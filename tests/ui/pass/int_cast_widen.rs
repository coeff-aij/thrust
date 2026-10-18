//@check-pass
//@compile-flags: -C debug-assertions=off

// A widening `as` gives its result the target type: `-y` is an `i32`, not a `u8`, and the loop
// head, which assumes the facts of its arguments' types, must not assume it non-negative.

#[thrust::callable]
fn f(x: u8) {
    let y = -(x as i32);
    let mut i = 0;
    while i < 3 {
        i += 1;
    }
    assert!(y <= 0);
}

fn main() {}
