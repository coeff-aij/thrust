//@compile-flags: -Adead_code -C debug-assertions=off
// `#[thrust::opaque]` and `#[thrust::reveal]` stop where they would change nothing.

mod plain {
    #[thrust::opaque]
    pub fn not_a_predicate(x: i64) -> i64 { //~ ERROR: applies only to a predicate or logic function
        x
    }
}

mod with_opaque {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    pub fn small(x: i64) -> bool {
        x < 10
    }

    #[thrust::reveal]
    #[thrust::trusted]
    #[thrust::callable]
    pub fn trusted_reveals(x: i64) -> i64 { //~ ERROR: applies only to a function whose body Thrust analyzes
        x
    }
}

mod other {
    #[thrust::reveal]
    pub fn reveals_nothing(x: i64) -> i64 { //~ ERROR: this module has none
        x
    }

    #[thrust_macros::predicate]
    pub fn transparent(x: i64) -> bool {
        x > 0
    }

    #[thrust::reveal(transparent)] //~ ERROR: is not a `#[thrust::opaque]` function
    pub fn reveals_transparent(x: i64) -> i64 {
        x
    }

    #[thrust::reveal(crate::nowhere::f)] //~ ERROR: cannot find
    pub fn reveals_missing(x: i64) -> i64 {
        x
    }

    #[thrust::reveal(crate::hidden::secret)] //~ ERROR: is not visible here
    pub fn reveals_private(x: i64) -> i64 {
        x
    }
}

mod hidden {
    #[thrust_macros::predicate]
    #[thrust::opaque]
    fn secret(x: i64) -> bool {
        x > 0
    }
}

fn main() {}
