//@compile-flags: -C debug-assertions=off
// A function pointer that an analyzed function stores in a field of a recursive enum, behind a
// `&mut` a trusted body passes it, stops: the trusted body may call it with any argument.

fn g(x: i32) {
    assert!(x > 0);
}

enum Handler {
    Done,
    Call(fn(i32), Box<Handler>),
}

struct Table {
    first: Box<Handler>,
}

fn install(t: &mut Table) { //~ ERROR: which Thrust does not analyze
    t.first = Box::new(Handler::Call(g, Box::new(Handler::Done)));
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn run() {
    let mut t = Table {
        first: Box::new(Handler::Done),
    };
    install(&mut t);
    if let Handler::Call(f, _) = *t.first {
        f(0)
    }
}

fn main() {
    run()
}
