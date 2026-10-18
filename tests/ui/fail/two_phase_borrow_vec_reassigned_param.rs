//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `x.push(x.len())` through a `&mut Vec` parameter that is reassigned later.

fn push_len<'a>(mut x: &'a mut Vec<usize>, y: &'a mut Vec<usize>) {
    x.push(x.len());
    x = y;
    x.push(9);
}

fn main() {
    let mut v = Vec::new();
    v.push(0);
    let mut w = Vec::new();
    push_len(&mut v, &mut w);
    assert!(v.len() == 2);
    assert!(v[1] == 2);
}
