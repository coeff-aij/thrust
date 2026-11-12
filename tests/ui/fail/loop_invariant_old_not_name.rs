//@compile-flags: -C debug-assertions=off

// `old!` takes the name of a parameter, not an expression.

#[thrust_macros::context]
fn grow(v: Vec<i64>) -> Vec<i64> {
    let mut w = v;
    while w.len() < 3 {
        thrust_macros::invariant!(
            |w: Vec<i64>, old!(v.len()): usize| w.len() >= old!(v.len()) //~ ERROR: `old!` takes the name of a parameter
        );
        w.push(0);
    }
    w
}

fn main() {}
