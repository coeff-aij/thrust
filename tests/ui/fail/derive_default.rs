//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The Default::default spec says nothing about the value, so nothing about
// the fields can be concluded.

#[derive(Default, PartialEq)]
struct Settings {
    level: u8,
    enabled: bool,
    name: Option<i64>,
}

impl thrust_models::Model for Settings {
    type Ty = Settings;
}

fn main() {
    let s = Settings::default();
    assert!(!s.enabled);
}
