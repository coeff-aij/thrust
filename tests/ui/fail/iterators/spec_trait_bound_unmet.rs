//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:develop-2493045c3

// `Iterator::next` is specified for types implementing `IteratorSpec`; `Once<T>` does not, so
// its own `next` is analyzed.

struct Once<T>(Option<T>);

impl<T> Iterator for Once<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.0.take()
    }
}

fn first<T: thrust_models::Model + Copy + PartialEq>(x: T)
where
    T::Ty: PartialEq,
{
    let mut it = Once(Some(x));
    match it.next() {
        Some(y) => assert!(y != x),
        None => panic!(),
    }
}

fn main() {}
