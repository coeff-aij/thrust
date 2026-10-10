//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `pre!` of a trait method at a type parameter is the trait's precondition, which a call there
// takes too.

#[thrust_macros::context]
trait Get {
    #[thrust_macros::requires(x > 0)]
    #[thrust_macros::ensures(true)]
    fn get(&self, x: i64) -> i64;
}

struct One;

impl thrust_models::Model for One {
    type Ty = ();
}

impl Get for One {
    fn get(&self, x: i64) -> i64 {
        assert!(x > 0);
        x
    }
}

#[thrust_macros::requires(thrust_macros::pre!(<T as Get>::get(t, x)))]
#[thrust_macros::ensures(true)]
fn via<T: Get>(t: &T, x: i64) -> i64 {
    t.get(x)
}

fn main() {
    via(&One, 1);
}
