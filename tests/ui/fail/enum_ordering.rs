//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `core::cmp::Ordering` is `#[repr(i8)]` with `Less = -1`, so a hand-written `Ord::cmp` exercises
// discriminants that are neither 4 bytes wide nor non-negative.

use std::cmp::Ordering;

pub struct Size {
    bytes: i64,
}

impl thrust_models::Model for Size {
    type Ty = Size;
}

impl PartialEq for Size {
    fn eq(&self, other: &Size) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for Size {}

impl PartialOrd for Size {
    fn partial_cmp(&self, other: &Size) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Size {
    fn cmp(&self, other: &Size) -> Ordering {
        if self.bytes < other.bytes {
            Ordering::Less
        } else if self.bytes == other.bytes {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

fn main() {
    let a = Size { bytes: 1 };
    let b = Size { bytes: 2 };
    let n = match a.cmp(&b) {
        Ordering::Less => 1,
        Ordering::Equal => 2,
        Ordering::Greater => 3,
    };
    assert!(n == 2);

    let c = Size { bytes: 3 };
    let d = Size { bytes: 3 };
    let m = match c.cmp(&d) {
        Ordering::Less => 1,
        Ordering::Equal => 2,
        Ordering::Greater => 3,
    };
    assert!(m == 2);
}
