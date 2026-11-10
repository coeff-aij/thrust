//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60
// A capture whose type names `Self`, in a default method of a trait under `context`: the clause,
// lifted out of the trait, names `Self` under another name.
#[thrust_macros::requires(thrust_macros::pre!(f(&x)))]
#[thrust_macros::ensures(thrust_models::exists(|g| thrust_macros::post!(thrust_models::model::Mut::new(f, g)(&x), result)))]
fn call<F: FnMut(&i64) -> i64>(x: i64, mut f: F) -> i64 {
    f(&x)
}

fn id<T>(t: &T) -> &T {
    t
}

#[thrust_macros::context]
trait Tr: thrust_models::Model + Sized {
    #[thrust::callable]
    fn g(&self) -> i64 {
        let s = self;
        call(
            1,
            thrust_macros::closure!(
                captures(s: &mut &Self),
                requires(**s == **s),
                ensures(result == *x),
                |x: &i64| -> i64 {
                    id(s);
                    *x
                },
            ),
        )
    }
}

impl Tr for i64 {}

fn main() {
    let r = 1i64.g();
    let _ = r;
}
