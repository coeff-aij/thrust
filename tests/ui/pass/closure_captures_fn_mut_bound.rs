//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// A closure passed straight to `max_by_key`, whose `F: FnMut` bound makes it `FnMut` although its
// body only reads `dl`, holds `dl` behind a `&mut`.
#[derive(PartialEq)]
struct D {
    a: i64,
    b: i64,
}

impl thrust_models::Model for D {
    type Ty = D;
}

#[thrust_macros::requires(d.b >= 0)]
#[thrust_macros::ensures(true)]
fn avail(x: &i64, d: &D) -> i64 {
    *x + d.a
}

fn main() {
    let d = D { a: 3, b: 1 };
    let dl = &d;
    let a: Option<i64> = Some(3);
    let m = a.into_iter().max_by_key(thrust_macros::closure!(
        captures(dl: &mut &D),
        requires((**dl).b >= 0),
        ensures(true),
        |x: &i64| -> i64 { avail(x, dl) },
    ));
    let _ = m;
}
