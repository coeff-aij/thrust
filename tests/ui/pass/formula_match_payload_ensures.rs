//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// A `match` in an `ensures` binds the fields of tuple-like and struct-like variants.
enum Shape {
    Circle(i64),
    Rect { w: i64, h: i64 },
    Empty,
}

impl thrust_models::Model for Shape {
    type Ty = Self;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(match s {
    Shape::Circle(r) => result == r,
    Shape::Rect { w, h } => result == w + h,
    _ => result == 0,
})]
fn size(s: Shape) -> i64 {
    match s {
        Shape::Circle(r) => r,
        Shape::Rect { w, h } => w + h,
        Shape::Empty => 0,
    }
}

fn main() {
    let n = size(Shape::Rect { w: 2, h: 3 });
    assert!(n == 5);
}
