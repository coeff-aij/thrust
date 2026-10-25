//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// In a crate with an `Invariant` impl, generic bodies are analyzed at each instance a call
// reaches, and one with a written contract is verified over its type parameters as well.
struct C {
    n: u32,
}

impl thrust_models::Model for C {
    type Ty = Self;
}

#[thrust_macros::context]
impl Invariant for C {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 0
    }
}

// Nothing calls `f`; its written contract is still verified once over `T`.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn f<T>(x: T) {}

fn main() {}
