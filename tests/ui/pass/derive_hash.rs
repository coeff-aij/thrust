//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// A derived Hash impl hashes field by field through Hash::hash, which has a
// spec saying only that it does not panic.

use std::hash::{Hash, Hasher};

#[derive(Hash)]
struct Pair {
    a: i64,
    b: bool,
}

impl thrust_models::Model for Pair {
    type Ty = Pair;
}

struct CountingHasher {
    writes: i64,
}

impl thrust_models::Model for CountingHasher {
    type Ty = CountingHasher;
}

impl Hasher for CountingHasher {
    fn write(&mut self, _bytes: &[u8]) {
        self.writes += 1;
    }

    fn finish(&self) -> u64 {
        0
    }
}

fn main() {
    let p = Pair { a: 1, b: true };
    let mut h = CountingHasher { writes: 0 };
    p.hash(&mut h);
    assert!(h.writes >= 0 || h.writes < 0);
}
