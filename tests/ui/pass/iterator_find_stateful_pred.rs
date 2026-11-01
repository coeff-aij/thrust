//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// As the fail twin, over one item: the predicate is called once.
fn main() {
    let mut v: Vec<u64> = Vec::new();
    v.push(1);
    let mut n = 0u64;
    let mut it = v.iter();
    let m = it.find(thrust_macros::closure!(
        captures(n: &mut &mut u64),
        requires(*(*n) + 1 <= 1),
        ensures(*(!n) == *(*n) + 1 && !(!n) == !(*n) && !result),
        |x: &&u64| -> bool { n += 1; assert!(n <= 1); false },
    ));
}
