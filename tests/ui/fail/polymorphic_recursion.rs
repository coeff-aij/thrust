//@error-in-other-file: reuses its contract at types nested deeper than the recursion limit
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `f::<T>` calls `f::<W<T>>`, so the `clone` its reused contract dispatches at `T` is recorded at
// `W<T>`, `W<W<T>>`, ... without end. The analysis stops past the recursion limit.
use thrust_models::Model;
#[derive(Clone)]
struct W<T>(T);

impl<T: Model> Model for W<T> {
    type Ty = W<T::Ty>;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f<T: Clone + Model>(x: T, n: u32) {
    let _y = x.clone();
    if n > 0 {
        f(W(x), n - 1);
    }
}

fn main() {
    f(1i64, 3);
}
