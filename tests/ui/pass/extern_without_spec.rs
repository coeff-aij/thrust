//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_UNSPECIFIED_UNREACHABLE=1

// A function of another crate without a specification (`std::process::id`) may be called only
// where the call is unreachable.
fn f(x: i64) -> i64 {
    if x < 0 {
        return std::process::id() as i64;
    }
    x
}

fn main() {
    let _ = f(2);
}
