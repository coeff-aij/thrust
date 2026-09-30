//@check-pass
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

pub struct Shape {
    kind: Kind,
    len: i64,
}

impl thrust_models::Model for Shape {
    type Ty = Self;
}

#[thrust_macros::predicate]
fn is_unsized(kind: Kind) -> bool {
    matches!(kind, Kind::Unsized)
}

#[thrust_macros::requires(is_unsized(shape.kind) ==> shape.len > 0)]
#[thrust_macros::requires(matches!(shape, Shape { kind: Kind::Prefixed { .. }, .. }) ==> shape.len > 1)]
fn min_len(shape: Shape) -> i64 {
    match shape.kind {
        Kind::Sized => 0,
        Kind::Unsized => {
            assert!(shape.len > 0);
            1
        }
        Kind::Prefixed(..) => {
            assert!(shape.len > 1);
            2
        }
    }
}

fn main() {
    min_len(Shape { kind: Kind::Unsized, len: 1 });
    min_len(Shape { kind: Kind::Prefixed(0, 0), len: 2 });
}
