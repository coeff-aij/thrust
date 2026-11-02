//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_PER_INSTANCE_GENERICS=1

// With the context, the formula names variables of a type parameter.
#[thrust_macros::context]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn pick<T: Copy>(x: T, y: T, first: bool) -> T {
    let r = if first { x } else { x };
    thrust_macros::proof_assert!(|r: T, y: T| r == y);
    let _ = y;
    r
}

fn main() {
    assert!(pick(1, 2, true) == 1);
}
