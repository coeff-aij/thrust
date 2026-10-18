//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `Tr::ok` at `T` and at `Box<T>` are two trait predicates, which an impl may define differently,
// so `ok` of `x` says nothing of `ok` of `Box::new(x)`. They stay two after `Box` is read as its
// content.

#[thrust_macros::context]
trait Tr {
    #[thrust_macros::predicate]
    fn ok(self) -> bool;
}

#[thrust_macros::requires(T::ok(x))]
#[thrust_macros::ensures(<Box<T> as Tr>::ok(result))]
fn wrap<T: Tr>(x: T) -> Box<T>
where
    Box<T>: Tr,
{
    Box::new(x)
}

fn main() {}
