//@compile-flags: -C debug-assertions=off
// A `ref` binding in `captures` is checked like any other.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn call<F: FnOnce(i64) -> i64>(x: i64, f: F) -> i64 {
    f(x)
}

fn main() {
    let mut n = 1i64;
    let a = &mut n;
    call(
        1,
        thrust_macros::closure!(
            captures(ref a: i64), //~ ERROR: this `FnOnce` closure holds `a` at type `&mut i64`, which `captures` restates at another type (only shared references and boxes may differ)
            requires(true),
            ensures(true),
            move |x: i64| -> i64 {
                *a += x;
                x
            },
        ),
    );
}
