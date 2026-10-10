//@compile-flags: -Adead_code -C debug-assertions=off

// What would let a lemma fail to terminate, or `proof!` assume a contract nothing proves.

#[thrust_macros::lemma]
#[thrust_macros::ensures(false)]
fn circular(k: usize) {
    circular(k) //~ ERROR: a lemma calling itself needs #[thrust_macros::variant(..)]
}

#[thrust_macros::lemma]
#[thrust_macros::ensures(false)]
fn spin() {
    loop {} //~ ERROR: a lemma cannot contain a loop
}

fn helper() {}

#[thrust_macros::lemma]
fn calls_helper() {
    helper() //~ ERROR: a lemma calls only lemmas, logic functions, predicates and model operations
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(false)]
fn forged_entry(k: i64) {
    _thrust_lemma_rec_forged_entry(&1000, 0) //~ ERROR: a lemma's recursive call passes the lemma's own parameters as the entry values
}

#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(false)]
fn shadowed_entry(k: i64) { //~ ERROR: a lemma's recursive call passes the lemma's own parameters as the entry values
    let __thrust_entry_k = &1000;
    shadowed_entry(0)
}

#[thrust_macros::lemma]
fn takes_mut(_x: &mut i64) {} //~ ERROR: a lemma cannot take a `&mut`

struct Wrapped<'a>(&'a mut i64);

#[thrust_macros::lemma]
fn takes_wrapped_mut(w: Wrapped) { //~ ERROR: a lemma cannot take a `&mut`
    *w.0 = 5;
}

#[thrust_macros::lemma]
fn takes_closure<F: FnOnce(i64) -> i64>(f: F) {
    let _ = Some(1i64).map(f); //~ ERROR: a lemma calls only lemmas, logic functions, predicates and model operations
}

#[thrust_macros::lemma]
fn calls_back<T: Ord>(a: T, b: T) {
    let _ = std::cmp::max(a, b); //~ ERROR: a lemma calls only lemmas, logic functions, predicates and model operations
}

#[thrust_macros::lemma]
fn passes_function() {
    let _ = Some(1i64).map(diverges_at); //~ ERROR: a lemma calls only lemmas, logic functions, predicates and model operations
}

#[thrust_macros::lemma]
fn ping(k: usize) {
    pong(k)
}

#[thrust_macros::lemma]
fn pong(k: usize) {
    ping(k) //~ ERROR: mutual recursion between lemmas is not supported
}

#[thrust_macros::ensures(false)]
fn diverges() {
    loop {}
}

#[thrust_macros::ensures(false)]
fn diverges_at(_x: i64) -> i64 {
    loop {}
}

#[thrust_macros::lemma]
fn fact() {}

fn more_than_a_lemma_call(mut x: i64) -> i64 {
    if thrust_models::__proof_branch() { //~ ERROR: `__proof_branch()` is only the condition of a `proof!`, which makes one lemma call
        fact();
        x = 1;
    }
    x
}

fn kept_condition() -> bool {
    let taken = thrust_models::__proof_branch(); //~ ERROR: `__proof_branch()` is only the condition of a `proof!`, which makes one lemma call
    if taken {
        fact();
    }
    taken
}

fn main() {
    thrust_macros::proof!(diverges()); //~ ERROR: `__proof_branch()` is only the condition of a `proof!`, which makes one lemma call
}
