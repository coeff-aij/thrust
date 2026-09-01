//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
//@check-pass

// Minimal reproducer for duplicated CHC clauses.
//
// A `&mut self` method on a struct holding an `Option<i32>` produces many
// byte-identical clauses for a single `goto`/`switchInt` transition. See the
// analysis of the duplicated-clauses issue for details.

#[thrust_macros::context]
trait Container {
    #[thrust_macros::requires(Self::invariant(*self))]
    fn fetch(&mut self) -> Option<i32>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
}

struct Holder {
    slot: Option<i32>,
}

impl thrust_models::Model for Holder {
    type Ty = Holder;
}

#[thrust_macros::context]
impl Container for Holder {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        "true";
        true
    }

    fn fetch(&mut self) -> Option<i32> {
        match &mut self.slot {
            None => None,
            Some(v) => Some(*v),
        }
    }
}

fn main() {}