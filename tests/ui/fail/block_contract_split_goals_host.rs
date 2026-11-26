//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SPLIT=1 THRUST_VERIFY_ONLY=host

// A function marked `#[thrust::split_goals]` splits the goals of the functions its
// `block_contract!`s are hoisted into as well: the two `ensures` of the block fail, and each is a
// part of its own, so the run reports two errors. Without the marker passed on, the extracted
// function's goals fall into one part and one error is reported.
#[thrust_macros::context]
//~^ ERROR: Unsat
//~| ERROR: Unsat
#[thrust::split_goals]
#[thrust_macros::requires(x == 0 && y == 0)]
fn host(mut x: i64, mut y: i64) -> i64 {
    thrust_macros::block_contract!(
        |mut x: i64, mut y: i64| -> ()
            requires(x == 0 && y == 0),
            ensures(x == 2),
            ensures(y == 2),
        {
            x += 1;
            y += 1;
        }
    );
    x + y
}

fn main() {}
