//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// A closure type parameter inside a path type in a formula signature is modelled once: the
// `Holder<F>` result is `(Closure<F>,)`, so `result.0 == f` compares two `Closure<F>`.

use thrust_models::model::Closure;

struct Holder<F> {
    f: F,
}

impl<F> thrust_models::Model for Holder<F> {
    type Ty = (Closure<F>,);
}

#[thrust_macros::ensures(result.0 == f)]
fn hold<F: Fn()>(f: F) -> Holder<F> {
    Holder { f }
}

fn main() {}
