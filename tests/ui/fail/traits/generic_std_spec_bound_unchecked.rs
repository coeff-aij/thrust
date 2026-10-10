//@error-in-other-file: spec bound not satisfied
// Rejected, not Unsat. `number` is fully annotated, so it is verified once, generically; its call
// `j.enumerate()` assumes the spec bound of std.rs's `_extern_spec_iterator_enumerate`
// (`J: IteratorSpec`) at the type parameter `J`. The instance `number::<Bad>` reuses that
// contract, and `Bad` has no `IteratorSpec` impl, so the program is rejected, as a direct
// `Bad.enumerate()` finds no spec. Without the check it verified, while the spec it assumed does
// not hold of `Bad`, whose `next` panics natively.
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

struct Bad;

impl thrust_models::Model for Bad {
    type Ty = Self;
}

#[thrust_macros::context]
impl Bad {
    #[thrust_macros::requires(false)]
    fn next_bad(&mut self) -> Option<i64> {
        panic!()
    }

    #[thrust::extern_spec_fn]
    #[thrust_macros::requires(false)]
    fn _extern_spec_next(it: &mut Bad) -> Option<i64> {
        <Bad as Iterator>::next(it)
    }
}

impl Iterator for Bad {
    type Item = i64;

    fn next(&mut self) -> Option<i64> {
        self.next_bad()
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn number<J: Iterator<Item = i64>>(j: J) {
    let _ = j.enumerate();
}

fn main() {
    number(Bad);
}
