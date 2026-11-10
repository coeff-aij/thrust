//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// A capture whose type is a type parameter of the method, in a generic impl: the closure holds it
// in the method's generics and the clause names it in its own.
#[thrust_macros::requires(thrust_macros::pre!(f(&x)))]
#[thrust_macros::ensures(thrust_models::exists(|g| thrust_macros::post!(thrust_models::model::Mut::new(f, g)(&x), result)))]
fn call<F: FnMut(&i64) -> i64>(x: i64, mut f: F) -> i64 {
    f(&x)
}

fn id<T>(t: &T) -> &T {
    t
}

struct S<C>(C);

impl<C> S<C> {
    #[thrust_macros::context]
    fn g<T: thrust_models::Model>(&self, t: &T) -> i64 {
        call(
            1,
            thrust_macros::closure!(
                captures(t: &mut &T),
                requires(true),
                ensures(result == *x),
                |x: &i64| -> i64 {
                    id(t);
                    *x
                },
            ),
        )
    }
}

fn main() {
    let s = S(0u8);
    let r = s.g::<i64>(&1i64);
    assert!(r == 1);
}
