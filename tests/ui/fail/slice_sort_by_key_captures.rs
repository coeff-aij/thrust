//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The pass twin with an entry outside the vector the key closure indexes.

fn main() {
    let mut weights: Vec<i64> = Vec::new();
    weights.push(5);
    weights.push(3);
    let mut order: Vec<usize> = Vec::new();
    order.push(1);
    order.push(2);
    order.sort_by_key(|&i| weights[i]);
    assert!(order.len() == 2);
}
