//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/polymorphic_recursion.rs`: `f` calls itself at its own type parameter.

#[derive(Clone)]
struct W<T>(T);

impl<T: thrust_models::Model> thrust_models::Model for W<T> {
    type Ty = W<T::Ty>;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f<T: Clone + thrust_models::Model>(x: T, n: u32) {
    let _y = x.clone();
    if n > 0 {
        f(x, n - 1);
    }
}

fn main() {
    f(1i64, 3);
}
