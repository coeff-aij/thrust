//@compile-flags: -Adead_code -C debug-assertions=off

// A variable a quantifier binds ranges over its type's values, but past the nesting limit of enum
// payloads the code points of a `char` cannot be stated: such a variable is rejected, so that
// assuming a statement true of every value assumes nothing false.
use thrust_models::forall;

type O9 = Option<Option<Option<Option<Option<Option<Option<Option<Option<char>>>>>>>>>;

fn main() {
    let x = 0i64;
    thrust_macros::assume!(|x: i64| x == 0 && forall(|o: O9| o != Some(Some(Some(Some(Some(Some(Some(Some(Some(char::MAX)))))))))));
    //~^ ERROR: cannot all be given their code points
    assert!(x == 1);
}
