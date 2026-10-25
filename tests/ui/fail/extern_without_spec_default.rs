//@compile-flags: -C debug-assertions=off

// Without `THRUST_UNSPECIFIED_UNREACHABLE=1`, a call of a function of another crate without a
// specification that is not on a panicking path stops the analysis.
fn f(x: i64) -> i64 {
    if x < 0 {
        return std::process::id() as i64; //~ ERROR: no specification of `std::process::id`
    }
    x
}

fn main() {
    let _ = f(2);
}
