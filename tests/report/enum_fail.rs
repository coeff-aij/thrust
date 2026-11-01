enum Shape {
    Square(i64),
    Rect(i64, i64),
}

fn area(s: Shape) -> i64 {
    match s {
        Shape::Square(a) => a * a,
        Shape::Rect(a, b) => a * b,
    }
}

fn positive(x: i64) -> Option<i64> {
    if x > 0 {
        Some(x)
    } else {
        None
    }
}

fn main() {
    let a = area(Shape::Rect(2, 3));
    if let Some(v) = positive(a) {
        assert!(v == 7);
    }
}
