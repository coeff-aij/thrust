trait Shape {
    fn area(&self) -> i64;
}

struct Square(i64);

impl Shape for Square {
    fn area(&self) -> i64 {
        self.0
    }
}

#[thrust_macros::lemma]
#[thrust_macros::ensures(true)]
fn trivial() {}

fn helper(x: i64) -> i64 {
    x
}

fn through_parameter<T: Shape>(shape: &T) -> i64 {
    shape.area()
}

fn through_closure(x: i64) -> i64 {
    let add = |y: i64| helper(y);
    add(x)
}

fn through_lemma() {
    thrust_macros::proof!(trivial());
}

fn uncalled() -> i64 {
    1
}

fn main() {
    helper(1);
    through_parameter(&Square(2));
    through_closure(3);
    through_lemma();
}
