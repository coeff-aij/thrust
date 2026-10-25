//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A derived `clone` keeps the invariant: its contract makes the result's model that of `*self`,
// whose invariant it requires (unlike a derived `Default`, `fail/type_invariant/derive_default.rs`).
#[derive(Clone)]
struct D {
    n: u32,
}

impl thrust_models::Model for D {
    type Ty = Self;
}

#[thrust_macros::context]
impl Invariant for D {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.n % 2 == 0
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result % 2 == 0)]
fn get(d: &D) -> u32 {
    d.n
}

fn main() {
    let d = D { n: 2 };
    let e = d.clone();
    assert!(get(&e) % 2 == 0);
}
