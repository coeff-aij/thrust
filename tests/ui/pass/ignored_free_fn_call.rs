//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/ignored_free_fn_call.rs`: the helper is analyzed.

fn helper(x: i32) -> i32 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn g() {
    let _ = helper(1);
}

fn main() {}
