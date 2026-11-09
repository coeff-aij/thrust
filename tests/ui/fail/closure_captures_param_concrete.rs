//@compile-flags: -C debug-assertions=off
// The closure holds `t` at `&mut &T`; restated at `&mut &i64`, the clause would read a `T` as an
// integer, which `g::<bool>` makes ill-sorted.
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
                captures(t: &mut &i64), //~ ERROR: this `FnMut` closure holds `t` at type `&mut &T`, and `captures` restates its part `T` at another type (only shared references and boxes may differ)
                requires(**t > 0),
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
    let r = s.g::<bool>(&true);
    assert!(r == 1);
}
