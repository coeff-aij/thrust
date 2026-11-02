fn fixed() -> i64 {
    let x = 1;
    thrust_macros::assume!(|x: i64| x == 2);
    x
}

fn with_closure(y: i64) -> i64 {
    let f = |z: i64| {
        thrust_macros::assume!(|z: i64| z > 0);
        z
    };
    thrust_macros::proof_assert!(|y: i64| y == y);
    f(y)
}

fn outer() -> i64 {
    fn inner() -> i64 {
        let v = 1;
        thrust_macros::assume!(|v: i64| v == 1);
        v
    }
    inner()
}

fn main() {
    assert!(fixed() == 2);
    assert!(with_closure(3) > 0);
    assert!(outer() == 1);
}
