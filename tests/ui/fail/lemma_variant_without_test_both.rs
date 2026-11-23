//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables

// Neither variant of `Result<(i64, Infallible), (i64, Infallible)>` has values, so rustc reads
// either one's field without a test. In a proof each read is an obligation that the value is of
// that variant, so reading both does not prove `false`.
use std::convert::Infallible;

#[thrust_macros::lemma]
#[thrust_macros::ensures(false)]
fn both(r: Result<(i64, Infallible), (i64, Infallible)>) {
    let Ok((n, _)) = r;
    let Err((m, _)) = r;
}

fn main() {}
