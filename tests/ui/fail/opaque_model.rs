//@compile-flags: -Adead_code -C debug-assertions=off

// The model counts the hits, an abstraction of the field, but the struct is not declared opaque.

use thrust_models::model::Int;

pub struct Counter {
    hits: Vec<u64>,
}

impl thrust_models::Model for Counter { //~ ERROR: is not the models of its fields in order
    type Ty = Int;
}

#[thrust_macros::context]
impl Counter {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == 0)]
    fn new() -> Counter {
        Counter { hits: Vec::new() }
    }

    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(!self == *self + 1)]
    fn hit(&mut self) {
        self.hits.push(0);
    }

    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == *self)]
    fn count(&self) -> usize {
        self.hits.len()
    }
}

fn main() {
    let mut c = Counter::new();
    c.hit();
    c.hit();
    assert!(c.count() == 2);
}
