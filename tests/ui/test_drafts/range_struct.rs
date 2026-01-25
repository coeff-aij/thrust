//@check-pass
//@compile-flags: -C debug-assertions=off

// error: verification error: Timeout(30s)

struct Range {
    start: i64,//usize,
    end: i64,//usize,
}

fn next(r: &mut Range) -> Option<i64> {
    if r.start < r.end {
        let item = r.start;
        r.start += 1;
        Some(item)
    } else {
        None
    }
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut count = 0;
    let mut sum = 0;
    while let Some(i) = next(&mut range) {
        // assert!(i + 1 == range.start);

        count += 1;
        sum += i;
    }
    // assert!(count == range.start);

    assert!(count == 5);
    assert!(sum == 10);
    // dbg!(count, sum);
}
