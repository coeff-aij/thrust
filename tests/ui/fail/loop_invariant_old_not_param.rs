//@compile-flags: -C debug-assertions=off

// `old!(x)` names a parameter of the function; `w` is a local.

#[thrust_macros::context]
fn grow(v: Vec<i64>) -> Vec<i64> {
    let mut w = v;
    while w.len() < 3 {
        thrust_macros::invariant!(
            |w: Vec<i64>, old!(w): Vec<i64>| w.len() >= old!(w).len() //~ ERROR: `w` is not a parameter of the function
        );
        w.push(0);
    }
    w
}

fn main() {}
