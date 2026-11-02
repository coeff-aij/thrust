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

fn main() {
    assert!(fixed() == 2);
    assert!(with_closure(3) > 0);
}
