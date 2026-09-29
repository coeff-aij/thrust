//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == a)]
fn max(a: i32, b: i32) -> i32 {
    a.max(b)
}

fn main() {
    let _ = max(1, 2);
}
