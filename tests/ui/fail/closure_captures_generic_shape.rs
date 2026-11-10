//@compile-flags: -C debug-assertions=off
// The closure holds `p` at a tuple of a type parameter and a `&mut`; restated as an integer, the
// shape differs, and with it the `&mut`.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn call<F: FnOnce(i64) -> i64>(x: i64, f: F) -> i64 {
    f(x)
}

#[thrust::callable]
#[thrust_macros::context]
fn g<T>(t: T, a: &mut i64) -> i64 {
    let p = (t, a);
    call(
        1,
        thrust_macros::closure!(
            captures(p: i64), //~ ERROR: this `FnOnce` closure holds `p` at type `(T, &mut i64)`, which `captures` restates at another type (only shared references and boxes may differ)
            requires(true),
            ensures(true),
            move |x: i64| -> i64 {
                let q = p;
                *q.1 += x;
                x
            },
        ),
    )
}

fn main() {
    let mut a = 1i64;
    g(0u8, &mut a);
}
