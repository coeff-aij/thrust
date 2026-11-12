//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::requires(i <= (*v).len())]
#[thrust_macros::ensures((!v).len() == (*v).len() + 1 && (!v)[i] == x + 1)]
fn insert_at(v: &mut Vec<u32>, i: usize, x: u32) {
    v.insert(i, x);
}

fn main() {}
