//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A field whose type is an associated type is dropped as the type it stands for: dropping `_h`
// runs `Guard`'s destructor, which panics.

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
    let _h = H::<()> { x: Guard(1) };
}
