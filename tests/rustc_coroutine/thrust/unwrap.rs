//! Rewrite (rewrites.md E3): `expect` becomes `unwrap_without_debug`, which needs no `Debug`.

pub trait Unwrap<T> {
    fn unwrap_without_debug(self) -> T;
}

impl<T, E> Unwrap<T> for Result<T, E> {
    fn unwrap_without_debug(self) -> T {
        let Ok(item) = self else {
            panic!();
        };
        item
    }
}

impl<T> Unwrap<T> for Option<T> {
    fn unwrap_without_debug(self) -> T {
        let Some(item) = self else {
            panic!();
        };
        item
    }
}
