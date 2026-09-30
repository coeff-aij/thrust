//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off -A unused-variables -A unused_parens
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=300 COAR_IMAGE=coar:9799dfd7b THRUST_TRY_SPECS=1

// `Size` of layout.rs: a struct model (`Ty = Self`) whose derived `Ord` compares the field, so
// `max` is specified through a local `PartialOrdSpec` that states that order.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Size {
    raw: u64,
}

impl thrust_models::Model for Size {
    type Ty = Self;
}

#[thrust_macros::context]
impl PartialOrdSpec for Size {
    #[thrust_macros::predicate]
    fn compares(self, other: Self, ord: Option<std::cmp::Ordering>) -> bool {
        (self.raw < other.raw && ord == Some(std::cmp::Ordering::Less))
            || (self.raw == other.raw && ord == Some(std::cmp::Ordering::Equal))
            || (self.raw > other.raw && ord == Some(std::cmp::Ordering::Greater))
    }

    fn compares_functional(
        a: &Self,
        b: &Self,
        x: Option<std::cmp::Ordering>,
        y: Option<std::cmp::Ordering>,
    ) {
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.raw > a.raw && result.raw >= b.raw && (result.raw == a.raw || result.raw == b.raw))]
fn larger(a: Size, b: Size) -> Size {
    a.max(b)
}

fn main() {}
