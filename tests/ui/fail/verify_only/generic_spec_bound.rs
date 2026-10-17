//@error-in-other-file: spec bound not satisfied
// Rejected, not Unsat. Only `h` is selected; `number` lies outside the selection but is generic,
// so it is still analyzed, and the spec bound its body assumes (`J: IteratorSpec`) is checked at
// the instance `number::<Bad>` that `h` makes. When generic defs outside the selection were
// trusted unread, this verified.
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_VERIFY_ONLY=h THRUST_SOLVER=tests/thrust-pcsat-wrapper

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

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn h() {
    number(Bad);
}

fn main() {}
