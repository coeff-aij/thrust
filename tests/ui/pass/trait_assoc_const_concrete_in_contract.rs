//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// An associated const at a concrete type has a value in a contract.
trait Tr {
    const K: i64;
}

struct B;

impl Tr for B {
    const K: i64 = 1;
}

#[thrust_macros::context]
#[thrust_macros::ensures(result == <B as Tr>::K)]
fn get() -> i64 {
    1
}

fn main() {
    assert!(get() == 1);
}
