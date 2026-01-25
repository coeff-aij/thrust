//@check-pass
//@compile-flags: -C debug-assertions=off

fn main() {
    let mut start = 0;
    let end = 5;

    let mut count = 0;
    let mut sum = 0;
    while start < end {
        count += 1;
        sum += start;
        start += 1;
    }

    assert!(count == 5);
    assert!(sum == 10);
}
