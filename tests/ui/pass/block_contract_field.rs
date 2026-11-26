//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
impl thrust_models::Model for S {
    type Ty = (thrust_models::model::Int, thrust_models::model::Int);
}

struct S {
    a: i64,
    b: i64,
}

fn main() {
    let mut s = S { a: 1, b: 5 };
    thrust_macros::block_contract!(
        |mut s: S| -> ()
        requires(s.0 == 1),
        ensures(old!(s).0 == 1 && s.0 == 2 && s.1 == old!(s).1),
        {
            s.a += 1;
        }
    );
    assert!(s.a == 2 && s.b == 5);
}
