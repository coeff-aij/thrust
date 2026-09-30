//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

#[derive(PartialEq)]
enum Wrapped {
    Zero,
    Value(i64),
}

impl thrust_models::Model for Wrapped {
    type Ty = Wrapped;
}

#[thrust_macros::logic]
fn reset(_w: Wrapped) -> Wrapped {
    Wrapped::Zero
}

#[thrust_macros::ensures(result == reset(w))]
fn clear(w: Wrapped) -> Wrapped {
    w
}

fn main() {
    let _ = clear(Wrapped::Value(1));
}
