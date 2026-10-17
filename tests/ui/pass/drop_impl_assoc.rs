//@check-pass
//@compile-flags: -C debug-assertions=off

// The twin of `fail/drop_impl_assoc.rs`: the destructor's assertion holds.

struct Guard(i32);

impl Drop for Guard {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

trait Tr {
    type Out;
}

impl Tr for () {
    type Out = Guard;
}

struct H<T: Tr> {
    x: T::Out,
}

fn main() {
    let _h = H::<()> { x: Guard(0) };
}
