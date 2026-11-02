//@compile-flags: -C debug-assertions=off

// A `static` with interior mutability may change, so its initializer says nothing of what a read
// sees.

use std::sync::atomic::{AtomicI64, Ordering};

static C: AtomicI64 = AtomicI64::new(0); //~ ERROR: reading the static `C` is not supported

fn main() {
    C.store(1, Ordering::Relaxed);
}
