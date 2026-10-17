#[thrust_macros::ensures(result <= v.len())]
fn count_pos(v: &Vec<i64>) -> usize {
    let mut c = 0;
    for x in v.iter() {
        if *x > 0 {
            c += 1;
        }
    }
    c
}

fn main() {
    let mut v = Vec::new();
    v.push(1);
    v.push(-2);
    assert!(count_pos(&v) <= 2);
}
