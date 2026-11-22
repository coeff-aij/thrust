//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A projection after an element that a slice pattern takes: a field of a tuple, the payload of
// an enum or an element of an array, read off the sequence at the element's position.

fn first_key(s: &[(i64, i64)]) -> i64 {
    if let [(k, _), ..] = s {
        *k
    } else {
        0
    }
}

fn last_value(s: &[(i64, i64)]) -> i64 {
    match s {
        [.., (_, v)] => *v,
        [] => 0,
    }
}

fn first_some(s: &[Option<i64>]) -> i64 {
    match s {
        [Some(x), ..] => *x,
        _ => 0,
    }
}

fn corner(m: &[[i64; 2]]) -> i64 {
    if let [[_, x], ..] = m {
        *x
    } else {
        0
    }
}

fn main() {
    let a = [(1, 2), (3, 4)];
    assert!(first_key(&a) == 1);
    assert!(last_value(&a) == 2);
    assert!(first_some(&[Some(5), None]) == 5);
    assert!(corner(&[[6, 7]]) == 7);
    let [(p, _), _] = a;
    assert!(p == 1);
}
