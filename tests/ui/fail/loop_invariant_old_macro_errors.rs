//@compile-flags: -C debug-assertions=off

// The errors `thrust_macros` gives at `old!`: an argument that is not a parameter's name, an
// `old!(x)` the formula reads without declaring it, and an `old!` outside a loop invariant.

#[thrust_macros::context]
fn not_a_name(v: Vec<i64>) -> Vec<i64> {
    let mut w = v;
    while w.len() < 3 {
        thrust_macros::invariant!(
            |w: Vec<i64>, old!(v.len()): usize| w.len() >= old!(v.len()) //~ ERROR: `old!` takes the name of a parameter
        );
        w.push(0);
    }
    w
}

#[thrust_macros::context]
fn undeclared(v: Vec<i64>) -> Vec<i64> {
    let mut w = v;
    while w.len() < 3 {
        thrust_macros::invariant!(
            |w: Vec<i64>| w.len() >= old!(v).len() //~ ERROR: the invariant reads `old!(v)` but does not declare it
        );
        w.push(0);
    }
    w
}

#[thrust_macros::context]
fn in_assert(v: Vec<i64>) -> Vec<i64> {
    let w = v;
    thrust_macros::proof_assert!(|w: Vec<i64>, old!(v): Vec<i64>| w.len() == old!(v).len()); //~ ERROR: only in `invariant!` and `partial_invariant!`
    w
}

fn main() {}
