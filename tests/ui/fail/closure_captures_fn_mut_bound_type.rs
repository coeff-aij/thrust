//@compile-flags: -C debug-assertions=off
// The `F: FnMut` bound of `call` makes the closure `FnMut`, which holds `dl` behind a `&mut`:
// restated as `&&D`, its type would not match the term `dl` names.
struct D {
    a: i64,
    b: i64,
}

impl thrust_models::Model for D {
    type Ty = D;
}

#[thrust_macros::requires(thrust_macros::pre!(f(&x)))]
#[thrust_macros::ensures(true)]
fn call<F: FnMut(&i64) -> i64>(x: i64, mut f: F) -> i64 {
    f(&x)
}

fn main() {
    let d = D { a: 3, b: 1 };
    let dl = &d;
    call(
        3,
        thrust_macros::closure!(
            captures(dl: &&D), //~ ERROR: this `FnMut` closure holds `dl` at type `&mut &D`, which `captures` restates at another type (only shared references and boxes may differ)
            requires((**dl).b >= 0),
            ensures(true),
            |x: &i64| -> i64 { *x + dl.a },
        ),
    );
}
