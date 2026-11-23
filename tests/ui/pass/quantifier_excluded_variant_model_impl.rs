//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A variant is excluded only where the variable's type as written has no value of it: below
// `Ghost<option::IntoIter<()>>`, whose model `Option<()>` comes from a `Model` impl, `Some` is kept,
// though `Option<Infallible>` beside it excludes `Some`. The assumed statement is true of Rust
// values (`p = (Some(()), None)`).
use std::convert::Infallible;
use thrust_models::{exists, Ghost};

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0
        && exists(|p: (Ghost<std::option::IntoIter<()>>, Option<Infallible>)| p.0 == Some(())));
    assert!(x == 0);
}
