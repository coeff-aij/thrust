//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The key closure indexes the vector it captures by `&`: `sort_by_key` asks its precondition at the
// states it reaches from the closure passed, whose capture is `weights`.

fn main() {
    let mut weights: Vec<i64> = Vec::new();
    weights.push(5);
    weights.push(3);
    let mut order: Vec<usize> = Vec::new();
    order.push(1);
    order.push(0);
    order.sort_by_key(|&i| weights[i]);
    assert!(order.len() == 2);
}
