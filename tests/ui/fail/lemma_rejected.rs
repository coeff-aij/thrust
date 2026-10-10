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
    helper() //~ ERROR: a lemma calls only lemmas and functions outside the crate
}

#[thrust_macros::lemma]
fn takes_mut(_x: &mut i64) {} //~ ERROR: a lemma cannot take a `&mut`

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

fn main() {
    thrust_macros::proof!(diverges()); //~ ERROR: `proof!` takes a call of a lemma
}
