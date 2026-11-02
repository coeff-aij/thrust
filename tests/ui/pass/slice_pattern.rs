//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Slice patterns on a shared slice and on an array: the length test reads the sequence's length,
// and an element or a subslice is read off the sequence at its position.

fn last(s: &[i64]) -> i64 {
    match s {
        [.., x] => *x,
        [] => 0,
    }
}

fn ends(s: &[i64]) -> i64 {
    match s {
        [a, .., b] => *a + *b,
        [a] => *a,
        [] => 0,
    }
}

fn rest_len(s: &[i64]) -> usize {
    match s {
        [_, rest @ ..] => rest.len(),
        [] => 0,
    }
}

fn pair(s: &[i64]) -> i64 {
    if let [a, b] = s {
        *a - *b
    } else {
        0
    }
}

fn main() {
    let a = [1, 2, 3];
    assert!(last(&a) == 3);
    assert!(ends(&a) == 4);
    assert!(rest_len(&a) == 2);
    assert!(pair(&[5, 2]) == 3);
    assert!(pair(&a) == 0);
    let [x, y, z] = a;
    let [p, rest @ ..] = a;
    assert!(x + y + z == 6 && p == 1 && rest[1] == 3);
}
