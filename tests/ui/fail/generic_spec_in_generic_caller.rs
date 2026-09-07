//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// `Tag::<V>::tag` carries no spec of its own and inherits the one written on the trait
// method. In `get` the generic arguments of the call are expressed in the caller's
// parameters, where `V` sits at index 1 because of the extra parameter `F`, while the
// resolved impl method only has a parameter at index 0.

#[derive(PartialEq)]
enum Tag<V> {
    A(V),
    B,
}

impl<V> thrust_models::Model for Tag<V> {
    type Ty = Tag<V>;
}

#[thrust_macros::context]
trait Tagged {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(result == 1)]
    fn tag(&self) -> i64;
}

#[thrust_macros::context]
impl<V> Tagged for Tag<V> {
    fn tag(&self) -> i64 {
        1
    }
}

fn get<F, V>(_f: F, t: &Tag<V>) -> i64 {
    t.tag()
}

fn main() {
    let t = Tag::<i64>::A(3);
    assert!(t.tag() == 2);
    let _ = get(1i64, &t);
}
