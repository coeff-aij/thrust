//@compile-flags: -C debug-assertions=off

// A destructor is verified, since Rust runs it wherever a value is dropped: it cannot be trusted
// or ignored.

struct Trusted(i32);

impl Drop for Trusted {
    #[thrust::trusted]
    #[thrust::callable]
    fn drop(&mut self) {} //~ ERROR: a `Drop::drop` takes no `requires` or `ensures`
    //~^ ERROR: a `Drop::drop` cannot be `#[thrust::trusted]` or `#[thrust::ignored]`
}

struct Ignored(i32);

impl Drop for Ignored {
    #[thrust::ignored]
    fn drop(&mut self) {} //~ ERROR: a `Drop::drop` cannot be `#[thrust::trusted]` or `#[thrust::ignored]`
}

fn main() {
    let _t = Trusted(0);
    let _i = Ignored(0);
}
