//@check-pass
//@compile-flags: -Aunused_parens -A unused-variables -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

// A partial closure reaching a call site through a generic trait impl.
//
// Two things have to happen at once here. `S<F>` implements a trait with an
// associated type, so the method's declared return type is a projection whose
// self type carries the closure; and the closure is partial, so `call` can only
// be entered where the closure's own precondition holds. `main` supplies the
// witness for that precondition from the adapter's postcondition rather than
// from a literal: all the caller knows about `v` is what `seeded` says.
#[thrust_macros::context]
trait Seeded {
    type Seed;

    #[thrust_macros::ensures(Self::seeded(result))]
    fn seed(&self) -> Self::Seed;

    #[thrust_macros::predicate]
    fn seeded(s: Self::Seed) -> bool;
}

struct S<F> {
    func: F,
}

impl<F> thrust_models::Model for S<F> {
    type Ty = S<thrust_models::model::Closure<F>>;
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> Seeded for S<F> {
    type Seed = i64;

    fn seed(&self) -> Self::Seed {
        1
    }

    #[thrust_macros::predicate]
    fn seeded(s: Self::Seed) -> bool {
        "(> s 0)";
        true
    }
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> S<F> {
    #[thrust_macros::requires(thrust_macros::pre!(((*self).func)(v)))]
    #[thrust_macros::ensures(thrust_macros::post!(((*self).func)(v), result))]
    fn call(&self, v: i64) -> i64 {
        (self.func)(v)
    }
}

fn main() {
    let s = S {
        func: thrust_macros::closure!(
            requires(x > 0),
            ensures(result == x + 1),
            |x: i64| -> i64 { x + 1 },
        ),
    };
    let v = s.seed();
    let r = s.call(v);
    assert!(r == v + 1);
}
