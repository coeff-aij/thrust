//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

use std::hash::{Hash, Hasher};

struct PanickingHasher;

impl thrust_models::Model for PanickingHasher {
    type Ty = PanickingHasher;
}

impl Hasher for PanickingHasher {
    fn write(&mut self, _bytes: &[u8]) {
        assert!(false);
    }

    fn finish(&self) -> u64 {
        0
    }
}

fn main() {
    let mut h = PanickingHasher;
    1i64.hash(&mut h);
}
