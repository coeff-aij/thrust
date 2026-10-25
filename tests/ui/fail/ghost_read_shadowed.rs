//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A ghost term reads `x` after an inner block shadowed it and a call ended that block: the name
// resolves by scope to the outer `x`, which is `5`, not the inner `6` `is_six` requires.
use thrust_models::Ghost;

#[thrust_macros::requires(g == 6)]
#[thrust_macros::ensures(true)]
fn is_six(g: Ghost<i64>) {}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == x)]
fn id(x: i64) -> i64 {
    x
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn shadow() {
    let x: i64 = 5;
    let y = {
        let x: i64 = 6;
        id(x)
    };
    let z = id(y);
    let g = thrust_macros::ghost!(|x: i64| -> i64 { x });
    is_six(g);
}

fn main() {
    shadow();
}
