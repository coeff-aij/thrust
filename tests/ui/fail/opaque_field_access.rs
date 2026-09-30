//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// A verified body reading `words` would read the model's sequence, which has one entry per
// element, as the field: Thrust would accept the assertion, which fails at run time.

use thrust_models::model::{Int, Seq};

#[thrust::opaque]
pub struct Bits {
    domain_size: usize,
    words: Vec<u64>,
}

impl thrust_models::Model for Bits {
    type Ty = (Int, Seq<Int>);
}

#[thrust_macros::context]
impl Bits {
    #[thrust::trusted]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result.0 == domain_size && result.1.len() == domain_size)]
    fn new_empty(domain_size: usize) -> Bits {
        Bits { domain_size, words: vec![0; domain_size.div_ceil(64)] }
    }

    fn num_words(&self) -> usize {
        self.words.len() //~ ERROR: accesses the field `words` of the opaque type `Bits`
    }
}

fn main() {
    let s = Bits::new_empty(100);
    assert!(s.num_words() == 100);
}
