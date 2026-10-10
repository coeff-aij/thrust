//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The derived `eq` of an enum compares the variants and then their fields.

#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    Empty,
    Line(i32),
    Rect { w: u8, h: u8 },
}

fn main() {
    let a = Shape::Rect { w: 2, h: 3 };
    let b = a.clone();
    assert!(a == b);
    assert!(a != Shape::Rect { w: 2, h: 3 });
    assert!(Shape::Line(0) != Shape::Empty);
}
