//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:804d76744

// The model reads `words` as one entry per element, the way the case study's bit-set
// contracts do. It has the sort of the fields, so the verified body of `num_words` reads the
// model's sequence as the field: Thrust accepts the assertion, which fails at run time
// (`words` holds `100.div_ceil(64) == 2` entries). positional_read_false_alarm.rs is the
// correct program, which Thrust refutes.

use thrust_models::model::{Int, Seq};

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
        self.words.len()
    }
}

fn main() {
    let s = Bits::new_empty(100);
    assert!(s.num_words() == 100);
}
