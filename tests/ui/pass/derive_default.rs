//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// A derived Default impl builds each field through Default::default, which
// has a spec saying only that it does not panic.

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
    assert!(s.enabled || !s.enabled);
}
