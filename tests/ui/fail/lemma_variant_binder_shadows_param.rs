//@compile-flags: -Adead_code -C debug-assertions=off

// A variant that binds the name of a lemma's parameter is rejected: its reads of the name would be
// the binder's, which the substitution by the parameter's entry value cannot tell apart.
#[thrust_macros::lemma]
#[thrust_macros::variant(match m { n => n })] //~ ERROR: a variant cannot bind `n`
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(false)]
fn f(n: i64, m: i64) {
    f(n, n - 1);
}

fn main() {}
