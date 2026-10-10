//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// In an `ensures`, a parameter denotes its value at the call, also after the body moves it.

#[thrust_macros::requires(b <= v.len())]
#[thrust_macros::ensures(result.len() >= v.len() - b)]
fn skip_some(v: Vec<u32>, b: usize) -> Vec<u32> {
    let mut out = Vec::new();
    let mut skipped = 0;
    for x in v {
        if skipped < b {
            skipped += 1;
        } else {
            out.push(x);
        }
    }
    out
}

fn main() {}
