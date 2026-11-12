//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust_macros::ensures((!v).len() == (*v).len() + 1 && (!v)[0] == x)]
fn push_front(v: &mut Vec<u32>, x: u32) {
    v.insert(0, x);
}

#[thrust_macros::requires(i <= (*v).len())]
#[thrust_macros::ensures((!v).len() == (*v).len() + 1 && (!v)[i] == x)]
fn insert_at(v: &mut Vec<u32>, i: usize, x: u32) {
    v.insert(i, x);
}

fn main() {
    let mut v = Vec::new();
    v.push(1u32);
    v.push(3);
    v.insert(1, 2);
    assert!(v.len() == 3 && v[0] == 1 && v[1] == 2 && v[2] == 3);
}
