//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables -A dead_code
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// An impl with no function leaves the derived `r` out: its rule is the inherited law `r_refl`,
// analyzed under the impl itself.

#[thrust_macros::context]
trait Rel {
    #[thrust_macros::predicate(derived)]
    fn r(self, o: Self) -> bool;

    #[thrust_macros::law]
    #[thrust_macros::ensures(Self::r(*a, *a))]
    fn r_refl(a: &Self) {}
}

#[derive(PartialEq, Clone, Copy)]
struct S {
    a: isize,
}

impl thrust_models::Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Rel for S {}

#[thrust_macros::requires(S::r(x, y))]
#[thrust_macros::ensures(true)]
fn use_r(x: S, y: S) {}

fn main() {}
