trait Visit {
    fn visit(&mut self, node: i64);
}

struct Counter;

impl Visit for Counter {
    #[thrust_macros::law]
    fn visit(&mut self, node: i64) {}
}

fn main() {}
