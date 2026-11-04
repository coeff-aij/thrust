//@compile-flags: -C debug-assertions=off

// A ghost term's parameter has the type of the variable it names: `b` is a `bool`, not an `i64`.

use thrust_models::model::Int;

fn main() {
    let b = true;
    let g = thrust_macros::ghost!(|b: i64| -> Int { b + 1 }); //~ ERROR: ghost! gives `b` the type `i64`, but it has the type `bool` here
    let _ = b;
}
