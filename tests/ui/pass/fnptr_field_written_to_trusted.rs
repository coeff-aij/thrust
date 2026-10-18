//@check-pass
//@compile-flags: -C debug-assertions=off
// The twin of `fail/fnptr_field_written_to_trusted.rs`: the recursive enum holds data, not a
// function pointer, so following its fields finds nothing to stop at.

fn g(x: i32) {
    assert!(x > 0);
}

enum Handler {
    Done,
    Call(i32, Box<Handler>),
}

struct Table {
    first: Box<Handler>,
}

fn install(t: &mut Table) {
    t.first = Box::new(Handler::Call(1, Box::new(Handler::Done)));
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn run() {
    let mut t = Table {
        first: Box::new(Handler::Done),
    };
    install(&mut t);
}

fn main() {
    g(1);
    run()
}
