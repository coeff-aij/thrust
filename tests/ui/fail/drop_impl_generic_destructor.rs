//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_PER_INSTANCE_GENERICS=1

// A destructor of a generic type is checked once over its type parameters, also when generic
// defs are verified per instance: here only `Vec::clear` drops a `G<u8>`, at an instance that no
// call site of the crate reaches, and `G { n: 1, .. }` panics.

struct G<T> {
    n: i32,
    t: T,
}

impl<T> Drop for G<T> {
    fn drop(&mut self) {
        assert!(self.n == 0);
    }
}

impl<T> thrust_models::Model for G<T> {
    type Ty = Self;
}

fn main() {
    let mut v = Vec::new();
    v.push(G { n: 1, t: 0u8 });
    v.clear();
    std::mem::forget(v);
}
