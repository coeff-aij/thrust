//@compile-flags: -Adead_code -C debug-assertions=off

// A struct whose model is not the tuple of its fields' models: the derived `Hash` reads
// `self.words` as component 1 of the model, an `Int`, and passes it where `Vec<u64>`'s
// `Seq<Int>` is expected. Without the derive the frontend accepts the file.

use std::marker::PhantomData;
use thrust_models::model::Int;

#[derive(Hash)]
pub struct DenseBitSet<T> {
    domain_size: usize,
    words: Vec<u64>,
    marker: PhantomData<T>,
}

impl<T> thrust_models::Model for DenseBitSet<T> {
    type Ty = (Int, Int);
}

fn main() {}
