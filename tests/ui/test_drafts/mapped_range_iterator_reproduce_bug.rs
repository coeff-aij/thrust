//@check-pass
//@compile-flags: -C debug-assertions=off

struct ClosureContainer<F> {
    f: F,
}

fn main() {
    let mut mapped_range = ClosureContainer {
        f: || {}
    };
}
