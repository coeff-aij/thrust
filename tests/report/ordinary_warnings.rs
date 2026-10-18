trait Visit {
    fn visit(&mut self, node: i64);
}

struct Counter;

#[thrust_macros::context]
impl Visit for Counter {
    fn visit(&mut self, node: i64) {}
}

#[thrust_macros::lemma]
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures(n >= 0)]
fn trivial(n: i64) {
    let unused = n;
}

fn main() {
    Counter.visit(1);
}
