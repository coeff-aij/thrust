//@check-pass
//@compile-flags: -C debug-assertions=off

// A `str` has the null sort, so all strings have one model and a derived `==` over a struct
// holding one is not equality of models; the derived body is analyzed instead, and the `k`s
// differ.

struct Name(&'static str);

impl PartialEq for Name {
    #[thrust::trusted]
    #[thrust::callable]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(PartialEq)]
struct S {
    name: Name,
    k: i32,
}

fn main() {
    let s = S { name: Name("a"), k: 1 };
    let t = S { name: Name("b"), k: 2 };
    assert!(!(s == t));
}
