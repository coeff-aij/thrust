//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The Default::default spec says nothing about the value, so nothing about
// the fields can be concluded.
use thrust_models::Model;
#[derive(Default, PartialEq)]
struct Settings {
    level: u8,
    enabled: bool,
    name: Option<i64>,
}

impl Model for Settings {
    type Ty = Settings;
}

fn main() {
    let s = Settings::default();
    assert!(!s.enabled);
}
