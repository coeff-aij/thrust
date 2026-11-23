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

fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
    f(x)
}

fn passes_item(x: i64) -> i64 {
    apply(helper, x)
}

fn passes_closure(x: i64) -> i64 {
    apply(|y: i64| helper(y), x)
}

fn through_pointer(x: i64) -> i64 {
    let p: fn(i64) -> i64 = helper;
    p(x)
}

fn main() {
    helper(1);
    through_parameter(&Square(2));
    through_closure(3);
    through_lemma();
    passes_item(4);
    passes_closure(5);
    through_pointer(6);
}
