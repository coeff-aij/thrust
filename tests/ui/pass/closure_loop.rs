//@check-pass
//@compile-flags: -C debug-assertions=off

fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

fn main() {
    let mut i = 0;
    let mut s = 0;
    while i < 10 {
        let f = |x| i + x;
        s += apply(f, i * i);
        i += 1;
    }
    assert!(s > 0);

    // let mut i = 0;
    // let mut s = 0;
    // while i < 10 {
    //     let f = |x| -1 * (i + x);
    //     s += apply(f, i * i);
    //     i += 1;
    // }
    // assert!(s > 0);

    let mut i = 0;
    let mut j = 1;
    let mut s = 0;
    while i < 10 {
        let f = |x| -1 * (i * x + j);
        s += apply(f, i + i);
        i += 1;
        j *= 2;
    }
    assert!(s < 0);
}