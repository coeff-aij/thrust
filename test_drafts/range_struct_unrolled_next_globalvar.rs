//@check-pass
//@compile-flags: -C debug-assertions=off

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
    
    let mut item = if range.start < range.end {
        let i = range.start;
        range.start += 1;
        Some(i)
    } else {
        None
    };

    while let Some(i) = item {
        count += 1;
        sum += i;

        let item = if range.start < range.end {
            let i = range.start;
            range.start += 1;
            Some(i)
        } else {
            None
        };
    }
    // assert!(count == range.start);

    assert!(count == 5);
    assert!(sum == 10);
    // dbg!(count, sum);
}
