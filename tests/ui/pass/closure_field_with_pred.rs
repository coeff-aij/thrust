//@check-pass
//@compile-flags: -C debug-assertions=off

struct S<F> {
    f: F,
}

impl<F> S<F>
    where F: Fn(i32) -> i32
{
    fn apply(&self) -> i32 {
        (self.f)(1)
    }


    #[thrust::predicate]
    fn truthy(self) -> bool {
        "true"; true
    }
}

fn main() {
    let s = S {
        f: |x: i32| x + 1,
    };
    let x = s.apply();

    assert!(x == 2);
}
