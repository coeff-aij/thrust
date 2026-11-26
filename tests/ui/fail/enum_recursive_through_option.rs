//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// An enum that holds itself through another enum is dropped: the resolution of its payload stops
// where the enum recurs.
enum List {
    Nil,
    Cons(i64, Option<Box<List>>),
}

fn main() {
    let l = List::Cons(1, Some(Box::new(List::Nil)));
    let h = match &l {
        List::Cons(h, _) => *h,
        List::Nil => 0,
    };
    assert!(h == 2);
}
