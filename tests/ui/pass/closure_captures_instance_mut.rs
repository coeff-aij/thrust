//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 THRUST_PER_INSTANCE_GENERICS=1
// Analyzed at its instance, `g`'s clause sees `T` as `&mut i64`, while the closure holds `t` at
// `&mut T`: the parameter stands for the `&mut` the restatement then shows.
#[thrust_macros::requires(thrust_macros::pre!(f(&x)))]
#[thrust_macros::ensures(thrust_models::exists(|h| thrust_macros::post!(thrust_models::model::Mut::new(f, h)(&x), result)))]
fn call<F: FnMut(&i64) -> i64>(x: i64, mut f: F) -> i64 {
    f(&x)
}

fn id<T>(t: &T) -> &T {
    t
}

#[thrust::callable]
#[thrust_macros::context]
fn g<T>(t: T) -> i64 {
    call(
        1,
        thrust_macros::closure!(
            captures(t: &mut T),
            requires(true),
            ensures(true),
            move |x: &i64| -> i64 {
                id(&t);
                *x
            },
        ),
    )
}

fn main() {
    let mut n = 0i64;
    g::<&mut i64>(&mut n);
}
