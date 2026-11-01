//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// `v[0]` captures `*v`, a deref of the reference parameter `v`, so the clauses name `v` with its
// type `&Vec<i32>`.
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
    assert!(r == 12);
    r
}

fn main() {
    let mut v = Vec::new();
    v.push(5);
    add_first(&v);
}
