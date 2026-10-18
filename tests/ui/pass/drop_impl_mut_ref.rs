//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_mut_ref.rs`: the destructor's write reaches `a`.

struct W<'a>(&'a mut i32);

impl Drop for W<'_> {
    fn drop(&mut self) {
        *self.0 = 7;
    }
}

fn main() {
    let mut a = 0;
    {
        let _w = W(&mut a);
    }
    assert!(a == 7);
}
