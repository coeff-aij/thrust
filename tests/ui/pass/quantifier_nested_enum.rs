//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variable of an enum whose payload holds the enum at ever larger arguments (`Nest<(T, T)>` in
// `Nest<T>`): its guard and the enums it registers stay finite. (A query that applies such a
// datatype cannot declare its instances, which is not supported.)
use thrust_models::forall;

enum Nest<T> {
    Flat(T),
    Deep(Box<Nest<(T, T)>>),
}

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && forall(|n: Nest<u64>| true));
    assert!(x == 0);
}
