//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/traits/unbox_forall_pred.rs`: the box holds `x`, of which `ok` holds.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::predicate]
    fn ok(self) -> bool;
}

#[thrust_macros::requires(T::ok(x))]
#[thrust_macros::ensures(T::ok(*result))]
fn wrap<T: Tr>(x: T) -> Box<T>
where
    Box<T>: Tr,
{
    Box::new(x)
}

fn main() {}
