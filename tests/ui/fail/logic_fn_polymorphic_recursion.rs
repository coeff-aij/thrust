//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
// A logic function calling itself at other type arguments (`Option<A>`) is reported, not followed
// without end by the precomputation of the contracts a contract names.

#[thrust_macros::logic]
#[thrust_macros::variant(n)]
fn depth<A>(n: i64) -> i64 {
    if n <= 0 {
        0
    } else {
        depth::<Option<A>>(n - 1) //~ ERROR: a logic function can call itself only at its own type arguments
    }
}

#[thrust_macros::ensures(result == depth::<i64>(x))]
fn f(x: i64) -> i64 {
    0
}

fn main() {
    f(0);
}
