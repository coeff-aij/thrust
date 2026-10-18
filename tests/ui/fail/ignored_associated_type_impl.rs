//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// `first`'s trusted contract relies on `C::IntoIter`'s `next`, which at `Coll` is `It`'s ignored
// one: an associated type's impl, not a nested obligation of `Coll`'s impl.

struct It;

impl Iterator for It {
    type Item = i32;
    #[thrust::ignored]
    fn next(&mut self) -> Option<i32> { //~ ERROR: a verified function can run it
        unimplemented!()
    }
}

struct Coll;

impl IntoIterator for Coll {
    type Item = i32;
    type IntoIter = It;
    fn into_iter(self) -> It {
        It
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn first<C: IntoIterator>(c: C) -> bool {
    c.into_iter().next().is_some()
}

fn main() {
    first(Coll);
}
