//@compile-flags: -C debug-assertions=off
// `closure_captures_generic_impl.rs` with `t` restated without the `&mut` the `FnMut` kind adds:
// the type parameter under it does not hide the missing `&mut`.
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
                captures(t: &T), //~ ERROR: this `FnMut` closure holds `t` at type `&mut &T`, which `captures` must restate up to shared references and boxes
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
