//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `wrap` calls the recursive `cnt`: the check of `wrap`'s definition assumes `cnt`'s result has
// the facts of `usize`, which `cnt`'s own definition guarantees, so `cnt(n) >= 0` needs no
// induction there.
#[thrust_macros::logic]
#[thrust_macros::variant(n)]
fn cnt(n: usize) -> usize {
    if n <= 0 {
        0
    } else {
        cnt(n - 1) + 1
    }
}

#[thrust_macros::logic]
fn wrap(n: usize) -> usize {
    cnt(n)
}

#[thrust_macros::ensures(result == wrap(n))]
fn f(n: usize) -> usize {
    cnt_rt(n)
}

fn main() {}

#[thrust_macros::ensures(result == cnt(n))]
fn cnt_rt(n: usize) -> usize {
    if n == 0 { 0 } else { cnt_rt(n - 1) + 1 }
}
