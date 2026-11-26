//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `&mut`s moved out of an array by a slice pattern: each binding takes the element's reference,
// so a write through it reaches the referent.

fn set_both(arr: [&mut i64; 2]) {
    let [a, b] = arr;
    *a = 1;
    *b = 2;
}

fn main() {
    let mut x = 0;
    let mut y = 0;
    let [a, b] = [&mut x, &mut y];
    *a += 1;
    *b += 3;
    assert!(x == 1 && y == 3);
    set_both([&mut x, &mut y]);
    assert!(x == 1 && y == 2);
}
