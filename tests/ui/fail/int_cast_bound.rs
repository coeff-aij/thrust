//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `n >= 0` is redundant in Rust, but Thrust models every integer width with the
// mathematical integers and does not refine unsigned types with non-negativity,
// so the truncation `n as u32` needs the lower bound stated explicitly.
#[thrust_macros::requires((n >= 0) && (n <= 4294967296usize))]
#[thrust_macros::ensures(result == n)]
fn narrow_in_range(n: usize) -> usize {
    let m = n as u32;
    m as usize
}

fn main() {
    assert!(narrow_in_range(4294967295) == 4294967295);
}
