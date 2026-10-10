//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A generic impl's method with a precondition of its own, which the trait's has to imply: a call
// through the trait checks only the trait's.

#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(x > 0)]
    #[thrust_macros::ensures(true)]
    fn get(&self, x: i64) -> i64;
}

struct W<T>(T);

impl<T> thrust_models::Model for W<T>
where
    T: thrust_models::Model,
{
    type Ty = (<T as thrust_models::Model>::Ty,);
}

#[thrust_macros::context]
impl<T> Get for W<T>
where
    T: thrust_models::Model,
    <T as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::requires(x > 0)]
    #[thrust_macros::ensures(result == x)]
    fn get(&self, x: i64) -> i64 {
        assert!(x > 0);
        x
    }
}

#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(true)]
fn via<T: Get>(t: &T, x: i64) -> i64 {
    t.get(x)
}

fn main() {
    via(&W(1i64), 1);
}
