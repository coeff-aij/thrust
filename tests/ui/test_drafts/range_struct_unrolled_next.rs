//@check-pass
//@compile-flags: -C debug-assertions=off

// error: verification error: Timeout(30s)

struct Range {
    start: i64,//usize,
    end: i64,//usize,
}

fn main() {
    let mut range = Range {
        start: 0,
        end: 5,
    };

    let mut count = 0;
    let mut sum = 0;
    loop {
        // assert!(range.start <= range.end);
        // assert!(count == range.start);

        let item = if range.start < range.end {
            let i = range.start;
            range.start += 1;
            Some(i)
        } else {
            None
        };

        match item {
            Some(i) => {
                // assert!(i + 1 == range.start);
                count += 1;
                sum += i;
            },
            None => break,
        };
    }
    // assert!(count == range.start);

    assert!(count == 5);
    assert!(sum == 10);
    // dbg!(count, sum);
}
