//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// `Iterator::next` is specified for types implementing `IteratorSpec`; `Once<T>` does not, so
// its own `next` is analyzed.

struct Once<T>(T, bool);

impl<T: Copy> Iterator for Once<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.1 {
            self.1 = false;
            Some(self.0)
        } else {
            None
        }
    }
}

fn first<T: thrust_models::Model + Copy + PartialEq>(x: T)
where
    T::Ty: PartialEq,
{
    let mut it = Once(x, true);
    match it.next() {
        Some(y) => assert!(y == x),
        None => panic!(),
    }
}

fn main() {
    first(1i64);
}
