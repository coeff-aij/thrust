//@compile-flags: -C debug-assertions=off
// The closure holds `u` at `U`; restated at the other type parameter `T`, its type would not match
// the term `u` names.
#[thrust_macros::requires(thrust_macros::pre!(f(x)))]
#[thrust_macros::ensures(true)]
fn call<F: FnOnce(i64) -> i64>(x: i64, f: F) -> i64 {
    f(x)
}

fn id<T>(t: T) -> T {
    t
}

#[thrust::callable]
#[thrust_macros::context]
fn g<T, U>(t: T, u: U) -> i64 {
    let _ = t;
    call(
        1,
        thrust_macros::closure!(
            captures(u: T), //~ ERROR: this `FnOnce` closure holds `u` at type `U`, which `captures` restates at another type (only shared references and boxes may differ)
            requires(true),
            ensures(true),
            move |x: i64| -> i64 {
                id(u);
                x
            },
        ),
    )
}

fn main() {
    g(0u8, 1u16);
}
