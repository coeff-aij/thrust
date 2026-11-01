//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `NonNull` has no `Model` impl, so its model is the tuple of its fields, an opaque raw pointer:
// all `NonNull`s have one model, and a derived `==` over a struct holding one is not equality of
// models; the derived body is analyzed instead, and `Ptr`'s `eq` says nothing. Natively `s == t`
// is false for two different pointers.

use std::ptr::NonNull;

struct Ptr(NonNull<i32>);

impl PartialEq for Ptr {
    #[thrust::trusted]
    #[thrust::callable]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(PartialEq)]
struct S {
    p: Ptr,
    k: i32,
}

#[thrust::callable]
fn check(x: NonNull<i32>, y: NonNull<i32>) {
    let s = S { p: Ptr(x), k: 1 };
    let t = S { p: Ptr(y), k: 1 };
    assert!(s == t);
}

fn main() {}
