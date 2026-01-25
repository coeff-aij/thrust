//@check-pass
//@compile-flags: -C debug-assertions=off

// error: verification error: Unknown { stdout: "unknown\n" }

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
    let mut item = None;
    loop {
        if range.start < range.end {
            let i = range.start;
            range.start += 1;
            item = Some(i);
        } else {
            item = None;
        }

        let Some(i) = item else {
            break;
        };

        count += 1;
        sum += i;
    }
    
    assert!(count == 5);
    assert!(sum == 10);
    // dbg!(count, sum);
}
