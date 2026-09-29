//@check-pass
//@compile-flags: -C debug-assertions=off

#[repr(u128)]
enum Tag {
    Low = 1,
    High = u128::MAX,
}

const PAIR: &(u128, i128) = &(u128::MAX, i128::MIN);

fn main() {
    let t = Tag::High;
    assert!(t as u128 == PAIR.0);
    assert!(PAIR.1 == -170141183460469231731687303715884105728);
}
