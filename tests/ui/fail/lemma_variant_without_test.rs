//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables

// rustc reads `Ok`'s field without testing the variant where `Err` has no values. A lemma's
// parameter ranges over its sort, which has `Err(())`, so in a proof the variant is an
// obligation, which nothing gives here.
use std::convert::Infallible;

#[thrust_macros::lemma]
#[thrust_macros::ensures(match r { Ok(_) => true, Err(_) => false })]
fn ok_by_let(r: Result<i64, Infallible>) {
    let Ok(n) = r;
}

#[thrust_macros::lemma]
#[thrust_macros::ensures(true)]
fn ok_by_match(r: Result<i64, i64>) {
    match r {
        Ok(n) => {
            let _m = n;
        }
        Err(m) => {
            let _m = m;
        }
    }
}

fn main() {}
