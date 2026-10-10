//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[derive(PartialEq, Debug)]
struct P {
    a: i64,
}

impl thrust_models::Model for P {
    type Ty = P;
}

#[thrust_macros::requires(p.a == q.a)]
fn same(p: P, q: P) {
    assert_eq!(p, q, "differ: {:?}", p);
}

fn main() {}
