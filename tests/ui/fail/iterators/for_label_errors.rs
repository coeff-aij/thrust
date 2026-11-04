//@compile-flags: -C debug-assertions=off

// A reference `iter!('l)` to a loop's ghost is resolved as `break 'l` is, and only to a `for`
// loop that has ghosts.

use core::ops::Range;

#[thrust_macros::context]
fn unknown_label(n: i64) {
    for _ in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>| iter!('rows).start >= 0); //~ ERROR: no loop labelled `'rows`
    }
}

#[thrust_macros::context]
fn while_label(n: i64) {
    let mut i = 0;
    'rows: while i < n {
        for _ in 0..n {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>| iter.start >= 0); //~ ERROR: `'rows` labels a `while` loop
        }
        i += 1;
    }
}

#[thrust_macros::context]
fn for_without_ghosts(n: i64) {
    'rows: for _ in 0..n {
        for _ in 0..n {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>| iter.start >= 0); //~ ERROR: `'rows` labels a `for` loop whose body does not start
        }
    }
}

#[thrust_macros::context]
fn from_closure(n: i64) {
    'rows: for _ in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>| iter.start >= 0);
        let g = || {
            for _ in 0..n {
                thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i64>| iter.start >= 0); //~ ERROR: no loop labelled `'rows`
            }
        };
        g();
    }
}

#[thrust_macros::context]
fn not_a_parameter(n: i64) {
    'rows: for _ in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>| iter.start >= 0);
        for _ in 0..n {
            thrust_macros::invariant!(|iter: Range<i64>| iter!('rows).start >= 0); //~ ERROR: is used in the formula but is not one of its parameters
        }
    }
}

#[thrust_macros::context]
fn mistyped(n: i64) {
    'rows: for _ in 0..n {
        thrust_macros::invariant!(|iter: Range<i64>| iter.start >= 0);
        for _ in 0..n {
            thrust_macros::invariant!(|iter: Range<i64>, iter!('rows): Range<i32>| iter.start >= 0); //~ ERROR: mismatched types
        }
    }
}

fn outside_context(n: i64) {
    'rows: for _ in 0..n {
        thrust_macros::invariant!(|iter!('rows): Range<i64>| iter!('rows).start >= 0); //~ ERROR: is resolved by `#[thrust_macros::context]`
    }
}

fn main() {}
