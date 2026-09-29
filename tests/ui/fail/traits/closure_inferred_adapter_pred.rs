//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:0360cb142

// A generic adapter's predicates instantiated at a closure whose contract is left to
// inference: the closure's precondition and postcondition unknowns appear in the
// predicates' definitions at that instantiation.
use thrust_models::model::Closure;

struct Apply<F> {
    func: F,
    arg: i64,
}

impl<F> thrust_models::Model for Apply<F> {
    type Ty = Apply<Closure<F>>;
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> Apply<F> {
    #[thrust_macros::predicate]
    fn ready(self) -> bool {
        thrust_macros::pre!((self.func)(self.arg))
    }

    #[thrust_macros::predicate]
    fn gives(self, r: i64) -> bool {
        thrust_macros::post!((self.func)(self.arg), r)
    }

    #[thrust_macros::requires(Self::ready(*self))]
    #[thrust_macros::ensures(Self::gives(*self, result))]
    fn run(&self) -> i64 {
        (self.func)(self.arg)
    }
}

fn main() {
    let a = Apply {
        func: |x: i64| x + 1,
        arg: 1,
    };
    assert!(a.run() == 3);
}
