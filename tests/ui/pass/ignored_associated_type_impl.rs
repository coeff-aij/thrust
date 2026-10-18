//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The twin of `fail/ignored_associated_type_impl.rs`: `It`'s `next` is analyzed.

struct It;

impl Iterator for It {
    type Item = i32;
    fn next(&mut self) -> Option<i32> {
        None
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
