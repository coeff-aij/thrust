//@compile-flags: -C debug-assertions=off
// The closure holds `p` whole, a tuple with a `&mut` in it; restated without the `&mut`, its type
// would not match the term `p` names.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn call<F: FnOnce(i64) -> i64>(x: i64, f: F) -> i64 {
    f(x)
}

fn main() {
    let mut a = 1i64;
    let p = (&mut a, 2i64);
    call(
        1,
        thrust_macros::closure!(
            captures(p: (i64, i64)), //~ ERROR: this `FnOnce` closure holds `p` at type `(&mut i64, i64)`, which `captures` must restate up to shared references and boxes
            requires(p.1 > 0),
            ensures(true),
            move |x: i64| -> i64 {
                let q = p;
                *q.0 += x;
                q.1
            },
        ),
    );
}
