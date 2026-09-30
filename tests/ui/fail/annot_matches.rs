//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

#[derive(Clone, Copy)]
pub enum Kind {
    Sized,
    Unsized,
    Prefixed(i64, i64),
}

impl thrust_models::Model for Kind {
    type Ty = Self;
}

#[thrust_macros::requires(matches!(kind, Kind::Unsized) ==> n > 0)]
#[thrust_macros::ensures(matches!(result, Kind::Prefixed(..) | Kind::Sized))]
fn check(kind: Kind, n: i64) -> Kind {
    if let Kind::Unsized = kind {
        assert!(n > 0);
        kind
    } else {
        Kind::Prefixed(n, 0)
    }
}

fn main() {
    check(Kind::Unsized, 1);
    check(Kind::Sized, 0);
}
