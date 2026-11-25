//@error-in-other-file: takes its const generic parameters as implicit arguments
//@compile-flags: -C debug-assertions=off

fn go<const N: usize>(x: usize) -> usize {
    x + N
}

fn apply<F: Fn(usize) -> usize>(f: F) -> usize {
    f(1)
}

fn main() {
    apply(go::<3>);
}
