//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// The fail twin of closure_captures_ref_param.rs: the caller asserts a result the closure's
// `ensures` excludes.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(thrust_macros::post!(f(x), result))]
fn apply<F: FnOnce(i32) -> i32>(x: i32, f: F) -> i32 {
    f(x)
}

#[thrust_macros::requires(v.len() > 0 && v[0] == 5)]
fn add_first(v: &Vec<i32>) -> i32 {
    let f = thrust_macros::closure!(
        captures(v: &Vec<i32>),
        requires(v.len() > 0 && x > 0),
        ensures(result == x + v[0]),
        |x: i32| -> i32 { x + v[0] },
    );
    let r = apply(7, f);
    assert!(r == 13);
    r
}

fn main() {
    let mut v = Vec::new();
    v.push(5);
    add_first(&v);
}
