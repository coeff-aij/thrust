//@compile-flags: -C debug-assertions=off
// The `F: FnMut` bound of `max_by_key` makes the closure `FnMut`, which holds `dl` behind a
// `&mut`: restated as `&&D`, its type would not match the term `dl` names.
struct D {
    a: i64,
    b: i64,
}

impl thrust_models::Model for D {
    type Ty = D;
}

fn main() {
    let d = D { a: 3, b: 1 };
    let dl = &d;
    let a: Option<i64> = Some(3);
    let m = a.into_iter().max_by_key(thrust_macros::closure!(
        captures(dl: &&D), //~ ERROR: this `FnMut` closure holds `dl` at type `&mut &D`, which `captures` must give it
        requires((**dl).b >= 0),
        ensures(true),
        |x: &i64| -> i64 { *x + dl.a },
    ));
    let _ = m;
}
