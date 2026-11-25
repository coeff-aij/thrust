//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The code under a block contract inside a loop starts from the contract's `requires` alone, also
// where it joins two paths: what holds of `n` at the loop's entry is not assumed there.

#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(true)]
fn f(n: i64, c: bool) {
    let mut i = 0_i64;
    while i < 3 {
        thrust_macros::invariant!(|i: i64| i >= 0);
        let _d = thrust_macros::block_contract!(requires(|| true), ensures(|| true), {
            let mut d = 0_i64;
            if c {
                d += 1;
            } else {
                d += 2;
            }
            assert!(n > 0);
            d
        });
        i += 1;
    }
}

fn main() {}
