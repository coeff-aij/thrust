//@error-in-other-file: is `#[thrust::ignored]`
//@compile-flags: -C debug-assertions=off

// A direct call of an ignored function, which has no type.

#[thrust::ignored]
fn helper(x: i32) -> i32 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g() {
    let _ = helper(1);
}

fn main() {}
