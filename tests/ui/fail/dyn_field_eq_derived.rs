//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A trait object is opaque, so all of them have one model and a derived `==` over a struct
// holding one is not equality of models; the derived body is analyzed instead, and `Obj`'s `eq`
// says nothing. Natively `s == t` is false.

trait Tr {
    fn id(&self) -> i32;
}

struct A(i32);

impl Tr for A {
    fn id(&self) -> i32 {
        self.0
    }
}

struct Obj<'a>(&'a dyn Tr);

impl<'a> PartialEq for Obj<'a> {
    #[thrust::trusted]
    #[thrust::callable]
    fn eq(&self, other: &Self) -> bool {
        self.0.id() == other.0.id()
    }
}

#[derive(PartialEq)]
struct S<'a> {
    d: Obj<'a>,
    k: i32,
}

#[thrust::callable]
fn check(x: &dyn Tr, y: &dyn Tr) {
    let s = S { d: Obj(x), k: 1 };
    let t = S { d: Obj(y), k: 1 };
    assert!(s == t);
}

fn main() {}
