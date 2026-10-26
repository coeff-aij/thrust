# Thrust

Thrust is a refinement type checking and inference tool for Rust.

## Getting Started

- Make sure [Z3](https://github.com/Z3Prover/z3) is installed.
- The main binary, `thrust-rustc`, behaves like `rustc` but includes Thrust's verification.
- In the following instructions, we assume the Thrust source code is cloned locally and commands are executed within it.

Take the following Rust code (`gcd.rs`):

```rust
fn gcd(mut a: i32, mut b: i32) -> i32 {
    while a != b {
        let (l, r) = if a < b {
            (&mut a, &b)
        } else {
            (&mut b, &a)
        };
        *l -= *r;
    }
    a
}

#[thrust::callable]
fn check_gcd(a: i32, b: i32) {
    assert!(gcd(a, b) <= a);
}

fn main() {}
```

Let Thrust verify that the program is correct. Here, we use `cargo run` in the Thrust source tree to build and run `thrust-rustc`. Note that you need to disable the debug overflow assertions in rustc, as they are currently not supported in Thrust.

```console
$ cargo run -- -Adead_code -C debug-assertions=false gcd.rs && echo 'safe'
   Compiling thrust v0.1.0 (/home/coord_e/rust-refinement/thrust)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.08s
     Running `target/debug/thrust-rustc -Adead_code -C debug-assertions=false gcd.rs`
error: verification error: Unsat

error: aborting due to 1 previous error
```

Thrust says the program is not safe (possible to panic). In fact, we have a bug in our `gcd` function:

```diff
 fn gcd(mut a: i32, mut b: i32) -> i32 {
     while a != b {
-        let (l, r) = if a < b {
+        let (l, r) = if a > b {
             (&mut a, &b)
         } else {
             (&mut b, &a)
```

Now Thrust verifies the program is actually safe.

```console
$ cargo run -- -Adead_code -C debug-assertions=false gcd_fixed.rs && echo 'safe'
    Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.08s
     Running `target/debug/thrust-rustc -Adead_code -C debug-assertions=false gcd.rs`
safe
```

Integration test examples are located under `tests/ui/` and can be executed using `cargo test`. You can review these examples to understand what the current Thrust implementation can handle.

The ui tests whose header sets `THRUST_SOLVER` to `tests/thrust-pcsat-wrapper` or `tests/thrust-spacer-wrapper` run CoAR in Docker, from the image `COAR_IMAGE` names (default `coar:latest`); `THRUST_UI_THREADS` sets how many tests run at once (default 8). With `THRUST_UI_SKIP_COAR=1` those tests are skipped and counted as filtered out, and only the tests Z3 decides run.

CI (`.github/workflows/ci.yml`) checks `cargo fmt` and `cargo clippy` and runs `cargo test` with `THRUST_UI_SKIP_COAR=1` and the Z3 that `.github/actions/setup-z3` pins: it has no CoAR image, so a ui test that needs PCSat is checked only locally. It runs on pushes to `main`, on pull requests, and on a manual run (`gh workflow run ci.yml --ref <branch>`); a newer run of the same ref cancels the one in progress. `.github/workflows/docs.yml` builds the API docs on every push to `main` and deploys them only from coord-e/thrust, the repository with GitHub Pages. `.github/workflows/claude-review.yml` reviews a pull request with the Claude API when someone with write access runs it with the pull request's number, from the Actions tab or with `gh workflow run claude-review.yml -f pr=<number>`. It needs the `ANTHROPIC_API_KEY` secret and without it only lists what it would send. Each review records its tool calls and tokens in an HTML comment at the end of its body; a run stops taking tool results once it has sent, cached or generated 500,000 tokens, and a run with no commit or reply since the latest review stops before calling the API. It runs the script and the prompt in `.github/` from the default branch, so a change to them takes effect once merged.

### Using Thrust with Cargo

Thrust can check Cargo projects and workspaces whose crates depend only on one another; external crates are not supported yet (#255), nor are members with a build script or proc-macro members, which cargo compiles to code. A contract is read in the crate it is written in, so a crate calling a function of another gives that function an extern spec, as `std.rs` does for the standard library (`tests/cargo/workspace`).

First, build Thrust in its source directory:

```sh
cargo build --bin thrust-rustc
```

Set up a project using the same Rust toolchain as Thrust (currently `nightly-2025-09-08`):

```sh
cargo +nightly-2025-09-08 new --edition 2021 thrust-example
cd thrust-example
```

Add assertions to your code. For example, write the following in `src/main.rs`:

```rust
fn add(x: i64, y: i64) -> i64 {
    x + y
}

fn main() {
    assert!(add(1, 2) == 3);
}
```

With Z3 on your `PATH`, set `RUSTC` to the absolute path of the built `thrust-rustc` binary and run:

```sh
RUSTC=/absolute/path/to/thrust/target/debug/thrust-rustc \
RUSTFLAGS='-C debug-assertions=false' \
cargo +nightly-2025-09-08 check
```

For the example above, the check succeeds. Changing the assertion to `add(1, 2) == 2` makes it fail with `verification error: Unsat` and a nonzero exit status.

Under `cargo check`, a crate that verifies goes on to write its metadata, as `rustc` would, so that the crates using it compile; one that fails writes none. Thrust records in each crate's dep-info the `THRUST_` variables with their values, the Thrust binary and the thrust-macros library, so that cargo checks a crate again when one of them or its sources change, and finds it fresh otherwise. What else decides a verdict is not tracked (the solver a command runs, the image of a wrapper): change `THRUST_CACHE_SALT` with it. The selection of `THRUST_VERIFY_ONLY` applies only to the packages cargo is asked to check, which cargo does not track, so a crate checked under a selection as such and then needed as a dependency is not checked again whole. A compilation asking for more than metadata (`cargo build`) stops after the verification: Thrust turns off MIR passes for its analysis that a program to run needs.

## Annotation

Thrust can verify a wide range of programs without explicit annotations, but you can use `#[thrust_macros::requires(expr)]` and `#[thrust_macros::ensures(expr)]` to annotate the precondition and postcondition of a function, aiding in verification or specifying the intended behavior. Here, `expr` is an ordinary Rust expression that Thrust interprets as a logical formula. It supports the usual integer, boolean, and comparison operators, integer constants such as `u64::MAX`, calls to functions declared with `#[thrust_macros::predicate]` (Boolean) or `#[thrust_macros::logic]` (any model type, a single expression), and the model operations described below.

`==` and `!=` in a formula, and in the body of a predicate or a logic function, are logical equality: they compare the models of their operands and need no `PartialEq` on them (`a == b` is written as `thrust_models::log_eq_args(&a, &b).log_eq()`). The operands are of one type, or of two types `thrust_models::LogEq` relates: two integer types, a model type and a type whose model it is, or a `Ghost<T>` and a type whose model is `T`'s. A `Ghost` has no `PartialEq`, so executable code cannot compare one.

```rust
#[thrust_macros::requires(n >= 0)]
#[thrust_macros::ensures((result * 2) == n * (n + 1))]
fn sum(n: i32) -> i32 {
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}
```

In an `ensures` expression, the special identifier `result` refers to the return value of the function. A parameter denotes the argument's value at the call, also where the body moves the argument or, for a `mut` parameter, assigns to it or lends it out as `&mut`; for a `&mut` parameter that value is the reference, described below. A written loop invariant (`thrust_macros::invariant!`) replaces what Thrust infers at its loop, so a postcondition that needs such an entry value past the loop has the invariant name it as a `thrust_models::FnParam`; a `thrust_macros::partial_invariant!` leaves it to inference. `requires` and `ensures` are independent: you can write either one on its own, and a missing one defaults to `true`.

A logic function may call itself (at its own type arguments, not through another function) when it carries `#[thrust_macros::variant(expr)]`, an integer expression over its parameters that does not call the function. Thrust emits the function as a `define-fun-rec` whose body carries the variant as a `:decreases` annotation, `(! body :decreases expr)`, which the solver takes as the function's termination measure, and adds clauses to the query requiring the variant to be non-negative and to decrease at each recursive call, under the conditions of the branches leading to it, so a variant that does not decrease is a verification error. A predicate cannot call itself; a recursive one is written as a logic function returning `bool`.

A logic function's value has the facts its result type states of every value: `>= 0` of an unsigned type, and with `THRUST_INT_RANGE` its range, also of the integers in tuples and enum payloads. A binding of a call's result is assumed to have them while the body's arithmetic is unbounded, so the query requires them of the body, in every mode, where the arguments have the quantifier-free facts of the parameters' types (the ranges of their integers, through tuples and references).

At other arguments the function is defined as a fixed value of its result type that has those facts (zero, an empty sequence, a variant of an enum built of such values; a part of the result type without facts keeps the body's value), so its value has them at any arguments.

In the body, a call of a logic function defined before, or of the function itself under the conditions on the way to the call (the induction hypothesis its variant makes well-founded), is assumed to have its result type's facts.

Not assumed in that check are the facts of a parameter's sequence elements or enum payloads (in every mode, so a result computed from a parameter's sequence elements, such as their sum at `usize`, cannot be shown `>= 0`), nor those of a trait's logic function applied at a type parameter (a law of the trait can state them); a result of a recursive enum holding such integers is an error. A function whose value may leave its result type's range on those grounds, or through its own arithmetic, returns `thrust_models::model::Int` instead.

```rust
#[thrust_macros::logic]
#[thrust_macros::variant(k)]
fn count_zeros(s: &[i64], k: usize) -> usize {
    if k <= 0 {
        0
    } else {
        count_zeros(s, k - 1) + if s[k - 1] == 0 { 1 } else { 0 }
    }
}
```

In a trait, a `#[thrust_macros::logic]` or `#[thrust_macros::predicate]` function may be declared without a body, and each implementation defines it with a function of the same kind. Where the trait is used through a type parameter, the function stands for every implementation (a universally quantified function in the query), so what is known of it there comes from the trait's contracts and its `#[thrust_macros::law]` functions, whose `requires`/`ensures` each implementation proves. An implementation may restate `#[thrust_macros::law]` on its proof (it must implement a law of the trait); a law, and a lemma, allow the lint of an unused parameter their contract mentions, and a law with an empty body that of every parameter.

A trait predicate declared with `#[thrust_macros::predicate(derived)]` (no body) may also be left out by an implementation for a type without type parameters. It is then an unknown the solver infers with the rest, as a loop invariant or an omitted contract is: every clause that mentions it (the implementation's `ensures` and laws, the clients' preconditions and assertions) is checked as with a written body, so a verdict gives the program's safety for whatever relation the solver picks, and says nothing else of that relation. The predicate depends on no forall predicate, and Thrust rejects a contract it assumes without checking it against a body (a trusted function, an extern specification, an inherited law not checked for its implementation) that mentions it or a predicate whose definition depends on it; an analyzed function whose precondition mentions it, entered from code Thrust does not analyze, must accept every argument there (`tests/ui/{pass,fail}/derived_pred/`).

A lemma, declared with `#[thrust_macros::lemma]`, is a function whose `requires`/`ensures` state a fact and whose body, verified like any other, proves it. A recursive call is the induction hypothesis and needs `#[thrust_macros::variant(expr)]`: the variant must be non-negative and decrease at each recursive call, checked where the call is made. A lemma must terminate and change nothing, so, as in Verus's proof functions and Creusot's ghost code, it calls only other lemmas (without mutual recursion), itself under its variant, logic functions, predicates and the model operations of `thrust_models`; it has no loop and no unsafe code, and takes no `&mut`, also not one inside a value. A lemma declared in a trait is defined by each impl with a lemma, and a lemma calls it only at a type that selects the impl, whose definition is the one checked. A block that rustc ends in `Unreachable`, such as a `match` on a value of an uninhabited type, must be unreachable in the logic, whose sorts are never empty, as in Creusot. A law's proof (an impl's definition of a `#[thrust_macros::law]`, or the trait's default body) follows the same rules, except that it may take a `&mut` and may use a law at a type parameter strictly inside the impl's self type (`T` of `Wrap<T>`), by calling it or a lemma that uses it at that parameter, but not at the self type itself. A trait's default body is checked so at each impl in the crate that inherits it, at the impl's arguments, and uses no law at a type parameter of the law itself; an impl in another crate is not checked. `thrust_macros::proof!(lemma(args))` uses a lemma in executable code: the analysis checks the lemma's precondition there and assumes its postcondition, and the program evaluates the arguments without running the call.

```rust
#[thrust_macros::lemma]
#[thrust_macros::variant(k)]
#[thrust_macros::ensures(count_zeros(s, k) <= k)]
fn count_zeros_bound(s: &[i64], k: usize) {
    if k > 0 {
        count_zeros_bound(s, k - 1);
    }
}

fn f(s: &[i64]) {
    thrust_macros::proof!(count_zeros_bound(s, s.len()));
    // count_zeros(s, s.len()) <= s.len() holds here.
}
```

### Mutable references

Within an annotation, a mutable reference `ma: &mut T` is modeled by its value at the time the function is called and its value when the function returns (the *prophecy* value). Use the deref operator `*ma` to denote the current value and the unary `!ma` to denote the final value. You can also construct a mutable-reference model directly with `thrust_models::model::Mut::new(current, final)`.

```rust
use thrust_models::model::Mut;

// `add` increments the referent by `a`. Equivalently, `!ma == *ma + a`.
#[thrust_macros::ensures(ma == Mut::new(*ma, *ma + a))]
fn add(ma: &mut i32, a: i32) {
    *ma += a;
}
```

### Type invariants

A type implementing `Invariant` (in `std.rs`, Creusot's trait) has its `invariant` predicate in every function's contract: required of each parameter of the type, or of the value behind a `&` or `&mut` parameter to it; ensured of the result (the value behind a returned reference) and of each `&mut` parameter's final value, unless the borrow may outlive the call, since the caller then sets the final value: the parameter's lifetime is named elsewhere in the signature (the result, another parameter, a `where` clause or bound, the parameter's own target), is `'static`, or the result holds an `impl Trait` or a trait object. An elided lifetime is the parameter's own. A body may break the invariant between its entry and its exits. Packing a value into a trait object requires its invariant too (see trait objects below). A trusted function's contract gets the same conjuncts, which its author must keep: one returning such a type promises its invariant. `#[thrust::open_inv]` on a parameter and `#[thrust::open_inv_result]` on a function leave out the parameter's and the result's. Closures, lemmas, laws and destructors (which take no precondition) get none; neither do values inside other types, nor a type parameter.

A contract established over type parameters therefore lacks the conjuncts the same contract has at an instance whose types hold a type with an `Invariant` impl (`W<T>` at `T := u32` when `W<u32>` has one). So in a crate with an `Invariant` impl every generic function with a body, trait default bodies and generic impls' methods included, is analyzed at each instance a call reaches, as `THRUST_PER_INSTANCE_GENERICS=1` asks for in any crate; one with a written contract is also verified once over its type parameters, so that it is checked even where no call reaches it. Code Thrust does not analyze (std, a trusted function, a derived method, the `clone` of a tuple) may not rely on an invariant either way: its contract may not promise one at an instance (`Option::<C>::unwrap`, a derived `Default`; a derived `clone` keeps it, since its result's model is `*self`'s), and it may not run a function of the crate whose contract requires one (`Option::<C>::clone` running `C::clone`, a derived `eq` of a struct running its field's), nor a generic destructor, checked once over its type parameters, at an instance that holds such a type (std's `unwrap_or` dropping a `W<C>`). These are errors, found by following what the crate can run as the check for ignored functions does; drop glue and the shims that forward a call run what they run on behalf of the code that entered them. A type holds one when, once normalized (which reveals an `impl Trait`), it or a type among its generic arguments, references, tuples, arrays, function pointers and the signatures of function items and closures has an invariant. A generic function with a written contract that calls a trait method on a value of a type parameter inside another type (a `Box<T>`, a field of `W<T>`) cannot state that value's invariant, so it does not verify at such a type; without a contract it can, since its contract is inferred at the instance (`tests/ui/{pass,fail}/type_invariant/generic_box.rs`). Creusot's structural invariant, abstract at a type parameter, which would let such a contract be verified once, is future work.

```rust
#[thrust_macros::context]
impl Invariant for Even {
    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        self.0 % 2 == 0
    }
}
```

### Refinement types

The conditions on `requires`/`ensures` are internally encoded as refinement types of the parameter and return types. You can also specify these refinement types directly. A refinement type is written `{ binder: type | formula }`, where `type` is a Rust type and `formula` constrains the value bound to `binder`. Use `#[thrust_macros::param(name: type)]` for a parameter and `#[thrust_macros::ret(type)]` for the return value:

```rust
#[thrust_macros::param(n: { x: i32 | x >= 0 })]
#[thrust_macros::ret({ x: i32 | (x * 2) == n * (n + 1) })]
fn sum(n: i32) -> i32 {
    if n == 0 {
        0
    } else {
        n + sum(n - 1)
    }
}
```

`#[thrust_macros::sig(..)]` is a shorthand that combines the parameter and return refinements into a single function-signature-shaped annotation:

```rust
#[thrust_macros::sig(fn(x: { v: i32 | v > 0 }) -> { r: i32 | r >= x })]
fn g(x: i32) -> i32 {
    x
}
```

Refinements may be nested inside generic arguments and reference types, e.g. `Box<{ v: i64 | v > 0 }>` or `&mut { v: i32 | v >= 0 }`.

A refinement on any parameter makes the precondition written, as `requires` does: it is the conjunction of the parameter refinements, a parameter without one is unconstrained, and the body is checked under it whether or not any function calls it. A parameter's refinement may refer only to the parameters before it. `param`, `ret` and `sig` cannot be combined with `requires` or `ensures` on one function.

### Loop invariants

`thrust_macros::invariant!(|x: i64, y: i64| x >= 1 && y >= 1)`, written in a loop body, gives the invariant of the innermost enclosing loop. Its closure's parameters name the variables live at the loop head, and a parameter typed `thrust_models::FnParam<T>` names a parameter of the function, read at entry with `.at_entry()`. Several `invariant!`s at one loop are conjoined. A written invariant is the whole invariant of its loop: Thrust infers nothing there, so it states every fact the rest of the function needs about the live variables and the parameters' entry values.

`thrust_macros::partial_invariant!(..)` takes the same closure and is conjoined with the invariant Thrust infers at the loop head instead. The written formula must still be inductive (together with what is inferred); it supplies a fact the solver does not find, while the rest of what holds at the loop stays inferred. A loop with a `partial_invariant!` treats its other `invariant!`s the same way. With `#[thrust_macros::context]` on the function, both forms may refer to generic- and `Self`-typed variables.

The bodies of functions marked with `#[thrust::trusted]` are not analyzed by Thrust. Additionally, `#[thrust::callable]` is an alias for `#[thrust_macros::requires(true)]` and `#[thrust_macros::ensures(true)]`. A function without a contract is checked only under the preconditions its callers establish: the body of one that nothing calls is not checked, and its clauses are left out of the query. Code Thrust does not analyze (a trusted body, a function outside `THRUST_VERIFY_ONLY` trusted for its contract, std code) may run such a function, a trait-method impl without a contract, or a closure as well, and adds nothing to what its callers establish; at each such entry the precondition is fixed instead, as an omitted `requires` is in Creusot, Verus and Prusti: to the `pre!` the entering contract states of it, and otherwise to `true` for every argument. A closure handed to such a function at a type parameter bounded by `Fn`, `FnMut` or `FnOnce` whose `pre!` the function's `requires` does not state must therefore accept every argument with the captures it is handed over with, and an `FnMut` closure the function may call more than once must do so at every state its calls reach from them; a generic function with a written contract that passes its closure on so must state `forall(|a| pre!(f(a)))`. A closure inside the iterator a function takes at a type parameter bounded by `IteratorSpec` (the closure of a `std::iter::Map` passed to `sum`) is handed over by that call too: the function runs it through the iterator's `next`, and the contract requires the iterator's `inv`, which for `Map` states the closure's `pre!` of every item it can be called on. A closure or function pointer that an analyzed function gives such code by returning it or storing it behind a `&mut` stops the analysis, unless it is a closure with a written `requires`, and so does a closure such code runs on a path where the analyzed call leading into it did not hand it over, whatever other calls hand it over. So does an entry into a function without a contract at a closure type of a trusted body, which has no contract to check the function against. A function marked `#[thrust::ignored]` is invisible to Thrust, as an `#[verifier::external]` item is to Verus: it is not analyzed, has no type, and no function Thrust verifies may run it. A direct call of one is an error, and so is an instance of one reachable from a verified function, through calls, trait methods, std functions, vtables, drop glue and derives, as rustc's monomorphization collector follows them from each function of the crate, verified or trusted (a generic one through the instances Thrust analyzes or reuses its contract at), from `main` and from the runtime's `start`, which reports what `main` returns. Thrust reads MIR without inlining at any optimization level, so a verified function inlined into a trusted one stays verified code. Static initializers are not followed: verified code cannot read a static (Thrust stops on it), and a static has no type parameters, so what a trusted body reaches through one is its author's fixed choice. This over-approximates what can run: an instance reached only on the way to a panic counts too, such as a hand-written `Debug::fmt` that `Result::unwrap` would print. A trusted body (`#[thrust::trusted]`, or a function outside `THRUST_VERIFY_ONLY` trusted for its contract) may run an ignored function itself, as Verus's `external_body` and Creusot's and Prusti's `#[trusted]` may, but a verified function it runs may not. A generic trusted function that verified code runs relies on the code its type parameters are instantiated with meeting its specification, so everything its body runs at that instance is verified code, its trait methods, closures, vtables, constants and shims, and its own calls too: such a body may not call an ignored function even at a fixed type. A non-generic trusted body is trusted throughout, and a derived impl is never trusted. A function pointer, trait object or closure that a trusted body hands out carries the trusted mode: calling it is the trusted author's responsibility. An ignored function cannot have a contract; to leave a body unchecked and still rely on a contract, write `#[thrust::trusted]`, which is then part of the trust base.

The methods rustc's built-in `#[derive(..)]`s generate are not analyzed either; each has the contract `std.rs` gives its trait method, which the derive implies. `PartialEq::eq` and `Clone::clone` are so treated when the type's model is the tuple (or enum) of its fields' models, or the model of its one field besides `PhantomData`s, and the fields' `==` and `clone` act on their models, and `Hash::hash`, `Default::default` and `Eq::assert_receiver_is_total_eq` (a no-op at run time) always. A type with a derived `PartialOrd` and no `PartialOrdSpec` impl is ordered as the derive orders it, lexicographically by its fields (a fieldless enum by its discriminants), when each field has a `PartialOrdSpec` order, so `<`, `cmp`, `max` and `min` need no annotation. A derived `Debug::fmt` is not verified, and a call to it is not supported.

A raw pointer, a trait object and a `str` are opaque: their model carries no information, so all values of such a type have one model. A type may hold one, as `fmt::Arguments` does, and verified code may pass it on, but dereferencing, comparing or casting a raw pointer and comparing strings are not supported (calls through a trait object are described below), and `==` on a type holding one of them is not taken as equality of models, also when it is held in the fields of a std type without a model of its own (`Rc`, `NonNull`), whose model is the tuple of its fields': a derived `PartialEq` of such a type is analyzed, and std's generic `PartialEq` contracts do not apply to it. For the same reason a specification may not compare such values with `==` or `!=` (it would hold of any two values, or of none), also inside a field of a type and at the type a generic contract is used at (a wrapper `W<T>` whose model is itself, used at `W<&str>`), a `Model` impl may not make one part of a model, and dereferencing, comparing, casting or taking a raw pointer in verified code stops with an error. A `&str` has no `Model`; a parameter of that type is named in a specification at the type `thrust_models::model::NoModel`, which can be neither compared nor passed on.

A function of another crate that has no specification, in `std.rs` or by an `extern_spec_fn`, has the precondition `false`, as Creusot gives an external function without a contract: a call to it must be unreachable. This is how a panic with a message is checked. `panic!`, `assert!`, `assert_eq!` and `unreachable!` with a message build a `fmt::Arguments` (a constant `&[&str; N]` of its pieces, `fmt::rt::Argument`s for its arguments) and call one of std's panic functions, all functions without a specification, so the branch that builds the message and panics must be unreachable, as the panic itself must. A call of such a function that returns, on a path that does not end in a call that does not return, and a function pointer made of one, whose calls are under the same rule, stop the analysis with `no specification`; with `THRUST_UNSPECIFIED_UNREACHABLE=1` Thrust warns there instead and checks the call to be unreachable. `Option::expect` and `Result::expect` have `unwrap`'s contracts.

```rust
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }
```

`#[thrust_macros::impl_trait_names(D, F)]` names the types of a function's argument-position `impl Trait` parameters, in order of occurrence, so that its `requires`/`ensures` can refer to them (e.g. `D::dl_of(*cx, dl)` for `cx: &impl HasDataLayout`); it may appear before or after them, and the number of names must equal the number of such parameters.

A method of a trait impl takes the trait's contract of that method: the one written on a local trait, or the one `std.rs` gives a std trait's method, such as `Iterator::next` for a type implementing `IteratorSpec`. A local trait method whose contract is not written in full (`requires` and `ensures`, `#[thrust::callable]`, or refinements of both a parameter and the result) gives an impl that overrides it none: the impl's contract is inferred from its own body, and a call resolved to the impl uses it. A refinement of only the parameters or only the result counts as not written: at a type parameter the method then has the unspecified type, which drops the written half there, a cost in completeness (`tests/ui/{pass,fail}/traits/default_param_refinement_at_param.rs`). With `#[thrust_macros::context]` on the impl, the method may carry `requires`/`ensures` of its own instead. Its body is then checked against them, a call resolved to the method uses them, and they must refine the trait's contract: the trait's precondition implies the method's, and the method's postcondition implies the trait's under the trait's precondition.

A trait object `&dyn Tr`, `&mut dyn Tr` or `Box<dyn Tr>` of a trait `Tr` of the crate is supported as an existential package (Mitchell and Plotkin, "Abstract Types Have Existential Type", 1988). A call through it takes `Tr`'s contract, as in Flux (the "Dynamic Trait Objects" section of its guide, `tests/tests/neg/trait_objects/dyn01.rs`). Verus (`source/rust_verify_test/tests/traits_dyn.rs`) takes the trait's contract too, but its coercion keeps the packed value, so a contract may read the receiver through the trait's spec functions. Creusot supports trait objects only of `core::fmt::Debug` and `core::fmt::Write` (`is_logically_dyn_compatible_trait` in `creusot/src/backend/clone_map/elaborator.rs`), translates the coercion as an uninterpreted `dyn_cast`, and gives a trait object a trivial invariant.

`Tr`'s contract is written with `requires`/`ensures` as for any trait (their companions are kept out of the vtable, so the trait stays dyn compatible; refinement-type annotations on a trait method make it not dyn compatible), and a contract may name a parameter of a trait-object type, whose model `thrust_models::model::Dyn` is opaque and cannot be compared.

The coercion of `&T`, `&mut T` or `Box<T>` to the trait object gives a fresh opaque value. It requires `T`'s type invariant of the value it packs, as a parameter of that type does, since the impl's methods assume it and a call through the trait object does not state it; this follows existential packing, where the packed value must have the type that the operations packed with it assume of the hidden representation. For the same reason it stops, when `T` has an invariant, at a method with a contract that takes `&mut self` and does not ensure the invariant of its final value: one whose `&mut self` is `#[thrust::open_inv]` or may outlive the call. A default body the impl does not override is analyzed at `T`, as generic bodies are in a crate with an invariant, and ensures it there. Packing at a type parameter (`fn pack<T: Tr>(x: Box<T>) -> Box<dyn Tr>`) requires nothing over the type parameter, which has no invariant; in a crate with an invariant the generic body is also analyzed at each instance, where packing requires the instance's. It checks each method of `T`'s impl that the vtable holds and `Tr` gives a contract against that contract, so an `#[thrust::ignored]` one stops it. The `&mut T` is moved into the trait object, so its final value stays free and the lender's value after the borrow is unknown, its type invariant included; a function cannot pass on a `&mut` parameter of a type with an invariant as a `&mut dyn Tr`, since it could not ensure the invariant of the parameter's final value. A coercion between trait objects that only drops auto traits (`dyn Tr + Sync` to `dyn Tr`) keeps the package.

A call through the trait object takes `Tr`'s contract of the method at `Self = dyn Tr`, which holds of every impl the call may reach as long as it does not mention `self` or `Self`. So a call through a trait object stops on a method without a written contract on `Tr` (one whose type is inferred from a default body included), and on a contract that mentions the receiver, `Self` or anything at `Self` (a logic function of `Tr`), which the opaque model would make false or vacuous.

Not supported, each stopping with an error:

- a trait object of a trait with laws, logic functions or predicates, or with `thrust_models::Model` as a supertrait, which fixes the receiver's model in its contracts;
- a type parameter instantiated with a trait object, written (`g::<dyn Tr>`) or through an impl the call resolves to (`impl<T: ?Sized + Tr> Tr for Box<T>` at `Box<dyn Tr>`), as Verus rejects an unsized blanket impl (this is checked at the calls Thrust analyzes: a default body whose contract a call through a trait object uses at `Self = dyn Tr` is not analyzed there, since the body that runs is the one at the packed type, but a method without a contract it calls through `Self` stops the analysis);
- trait objects of `std` traits and of the closure traits (`dyn Fn`), and of a trait with such a supertrait other than an auto trait (`trait Tr: Send + Sync` is supported);
- upcasting to a supertrait's trait object;
- trait objects made by another coercion (`Rc<dyn Tr>`, a `CoerceUnsized` struct);
- a constant holding a trait object.

An impl for a trait object itself (`impl Other for dyn Tr`) is an ordinary impl, checked at `Self = dyn Tr`.

A `Drop::drop` of the crate takes no precondition, as in Verus: Rust runs it wherever a value is dropped, also in code Thrust does not analyze, so it is checked once under `requires(true)`, over its type parameters, and its postcondition is inferred: a written `requires` or `ensures` on it is an error, and so is `#[thrust::trusted]` or `#[thrust::ignored]`. Where the crate drops a value, the destructor runs as rustc's drop glue runs it: the type's `drop`, then the drop of its fields in declaration order, each through one `&mut` of the value, so the effect `drop` has through a mutable reference it holds is what is then resolved. Where code Thrust does not analyze drops such a value (a function of `std`, a generic function used at an instance by its contract), the destructor's effect is unknown, and the prophecy of a mutable reference the value holds is left unresolved. A value inside a `ManuallyDrop`, or passed to `std::mem::forget`, is not dropped. A value whose drop runs such a destructor is not supported inside an enum, a `Box`, a collection or a closure that the crate drops.

A `for` loop runs over any type implementing `IteratorSpec` (`std.rs` gives one to ranges of integers, slice and `Vec` iterators, and `Enumerate`/`Zip` of them): `into_iter` of an iterator is the identity, and each step is `Iterator::next`'s contract. In a function under `#[thrust_macros::context]`, a loop invariant written as `thrust_macros::invariant!` or `thrust_macros::partial_invariant!` at the start of the loop body may name the iterator as `iter`, and also `iter_old`, the iterator before the loop, and `produced`, the ghost sequence of the items returned so far. The loop is then desugared as Creusot does, into a `loop` that steps `iter` by `next` after the invariant, and when `iter_old` or `produced` is named, `inv(iter)` and `produces(iter_old, produced, iter)` are conjoined to the invariant. The loop's own variables get names of their own and the invariant's `iter`, `iter_old` and `produced` are renamed to them, so the loop body still sees its variables of those names; an invariant of an inner loop names its own iterator and cannot name an outer one's. The type the invariant gives `iter` must be the iterator's.

`thrust_macros::pre!(f(args))` and `thrust_macros::post!(f(args), r)` name the precondition of `f` at `args` and its postcondition relating `args` to the result `r`, where `f` is a closure or a function named by path. For an `FnMut` closure state `c` (a `Closure<F>`), `pre!(c(args))` is its precondition at that state whatever state the call ends in, as Creusot's `FnMut` precondition takes the state by value: a call through `&mut` does not fix the final state. At a type parameter they read the trait-level contract a call there takes, such as `Iterator::next`'s for `I: IteratorSpec`. A trait method that has no such contract, called at a type parameter, accepts any arguments, and its result is related to them by a predicate that holds of every implementation, which `post!` names; so does one whose contract is inferred, wholly or in part, from its default body, since an impl that overrides the method is not checked against the default's type: `requires(forall(|r: &u64| post!(<F as Deref>::deref(&x), r) ==> *r > 0))` states what a body learns from `*x` at `F: Deref<Target = u64>`. At a concrete type, `pre!` and `post!` read the contract of the function the path resolves to, and a generic function verified once is accepted at an instance only if each such method its body calls, or its contract names by `pre!`, at a type parameter accepts any arguments there.

### Verifying part of a crate

`THRUST_VERIFY_ONLY=a::b,c::**,d::Type::method` verifies only the selected functions and assumes the contracts of the others, so that a large crate can be verified one part at a time. The variable is a comma-separated list of entries, each a path relative to the crate root (a leading `crate::` is allowed, and `crate` alone is the root module):

- a module selects the functions defined directly in it, not those of its submodules;
- `m::**` selects module `m` with all its submodules;
- any other path selects the named function with its closures, or every function defined inside the named item (a type's methods, a function's nested functions).

A method belongs to the module of its `impl` block and is named through the impl's self type, `module::Type::method`, for inherent and trait impls alike; a method of an impl for a type that is not a struct, enum or union is selected only through its module. The selection is the union of the entries, and an entry that selects no function is an error.

A function outside the selection that has a written contract (`requires`/`ensures`, `#[thrust::callable]`, or the contract of the trait method it implements) is treated as `#[thrust::trusted]`. One without a contract is still analyzed, because its callers use the contract inferred from its body. A generic function outside the selection is trusted unread too, so the spec bounds and trait methods its body assumes at its type parameters are not checked at the instances a selected caller makes; select it together with its callers, or verify the whole crate, for that check. A trait law that an impl outside the selection inherits is assumed there rather than checked. Predicates, logic functions and model declarations are unaffected, and so are `#[thrust::trusted]` and `#[thrust::ignored]`. Unset or empty, the whole crate is verified. Under cargo, the selection applies only to the packages cargo was asked to build (those it marks with `CARGO_PRIMARY_PACKAGE`); a path dependency built through Thrust is verified whole.

### Solving a crate in parts

`THRUST_SPLIT=<n>` solves each part of the constraints on its own, `n` parts at a time: a part is a class of clauses that share an unknown, directly or through a user-defined predicate that applies it. Parts constrain disjoint unknowns, so the crate is `sat` exactly when every part is, and `unsat` when one is; the solver's time limit applies to each part, and a part can take it longer or shorter than the whole query does. A function with a written contract shares no unknown with its callers, so its body and its callers are in different parts; a function left to inference is in the part of its callers. A failing part is reported by its number (from 1, as in JSON) with the functions its clauses come from, each by its lines; the clauses of one function can fall into several parts where they share no unknown, as on the two sides of a written annotation, and a note says so for the functions of a failing part, which are then also named with the lines the part's clauses were made at. The note after the errors counts the parts taken from `THRUST_CACHE_DIR` and lists those solved now. Empty or `0` solves one query. With `THRUST_SPLIT`, `THRUST_OUTPUT_DIR` gets each part's query as `thrust_output_part<i>.smt2`, numbered from 1 as the errors name the parts, and `THRUST_PRETTY_OUTPUT` is not made. `THRUST_REPORT` reports every part as the whole query is without `THRUST_SPLIT`: each part refuted is solved once more, asked for a refutation, and each part solved once more for its model when the report shows what is inferred there, `THRUST_SPLIT` at a time, when the solver gives refutations and models (`z3`); a second run that gives none is reported with what it gave; the JSON report also lists every part, with its number, its functions and the span of their clauses, its verdict and whether it came from `THRUST_CACHE_DIR`, and gives each failure the premises and the conclusion of its constraint. Fixing the code a failure points at and running again solves only the parts the fix changed.

`THRUST_CACHE_DIR=<dir>` keeps the verdict of each query solved, whole or in parts, so that a query that has not changed is not solved again. A query is keyed by its text, without comments and with the unknowns renamed in the order they first occur, and by the solver and the preprocessor commands with their arguments and `THRUST_CACHE_SALT`; set the salt to whatever else decides a verdict, such as the image a solver wrapper runs. Only `sat` and `unsat` are kept, and the report's model or refutation is never taken from it. Every part carries the forall predicates of the whole crate, so adding one anywhere changes the key of every part; of the datatypes it declares those of its own unknowns and definitions, and of the definitions of user predicates those its clauses reach.

### Reading what Thrust infers

`THRUST_REPORT` makes Thrust show, as notes at the code they belong to, the refinements it infers and the constraints it infers them from, for a person or a coding agent to read along with the program. `THRUST_REPORT=1` shows what is read first: the contracts and loop invariants inferred (`inferred`), when verification fails, the failure (`failure`), and what was checked of each function (`functions`), in either format. Otherwise the variable is a comma-separated list of items:

- `template`: the template of each contract left to inference, such as `fn inc(x: {int | inc.pre x}) -> {int | inc.post x result}`, and of each loop invariant, shown as the signature of its unknown over the variables live at the loop head, such as `sum.loop#1(n: int, i: int, s: int, old(n): int)`. Types are written as the sorts the constraints have them at (`int` for every integer type, `mut int` for `&mut i64`).
- `constraints`: the constraints each function and each loop contributes, each with what it checks (`argument of`, `loop entry`, `loop preservation`, `ensures`, `assertion`, …), where, and its formula over the program's variables, such as `(sum.loop#1 n i s n ∧ i < n) ==> sum.loop#1 n (i + 1) (s + 2) n`. A constraint is shown with the code it was made in; the unknowns it shares with other code are named after their template. A premise applying an unknown without arguments that every solution makes true, such as the one for reaching a function's entry, is left out.
- `solution`: the solver's interpretation of each unknown, such as `inc.pre x := x = 5`, and of a loop's unknown after its signature, `:= …`. `z3` simplifies each interpretation into an equivalent formula first (`(then qe simplify (repeat (then ctx-solver-simplify simplify) 10))`, within 5 seconds), and one it cannot simplify is shown as it answered.
- `inferred`: each contract and loop invariant with the solution substituted.
- `failure`: when verification fails, the constraint the solver refuted, at its span, the values its variables have where it fails, and the run of the program its refutation gives: each fact, an unknown at the concrete values of the arguments the program names (a `&mut x` as `*x` and `°x`, `…` for the others), above the facts it is derived from and with the constraint deriving it. A refuted `ensures`, `requires`, written loop invariant or parameter refinement a write through the parameter breaks (`*x = -1` against `param(x: &mut { v: i64 | v >= 0 })`) is shown where it fails, with the annotation it checks labelled, and a run through a call to a function with a written contract names that contract, whose `ensures` the run assumes. The refutation is asked of a second solver run on the same query with each goal marked, so the verdict is that of the query alone. The solver refutes one obligation of a query, so others may fail too; with `THRUST_SPLIT`, each part refuted gets its own. The refutation is then itself the error of the failed verification or part, `verification error: Unsat (thrust: refuted: …)` at the obligation (with `THRUST_REPORT_FORMAT=json`, the error is at the obligation); a failed part without one has its error at the code of the part, and its failure lines name it.
- `internal`: also the types of blocks that are not loop heads, intermediate steps of the analysis.
- `functions`: what the analysis did with the body of each function of the crate, closures included: `checked` (analyzed, over its type parameters or at an instance a call reaches), `trusted` (`#[thrust::trusted]`, or in a trusted function), `ignored` (`#[thrust::ignored]`), `unselected` (outside `THRUST_VERIFY_ONLY` with a written contract, which is assumed) or `not analyzed`, each with why (a generic function that `THRUST_PER_INSTANCE_GENERICS` leaves to the instances calls reach, when none does; a law of a trait no impl inherits); a checked body with the verdict of the query its clauses are in, or with `THRUST_SPLIT` of the parts they are in. A function is verified when its body is checked and that verdict is `sat`; `unsat` says only that a query holding its clauses is refuted, and the failure says where. A checked body none of whose clauses is in a part (with `THRUST_SPLIT`, `parts` empty) had nothing to check and is `sat`. Specification functions (predicates, logic functions, the companions of annotations, extern specs) and functions a macro writes (derives, `macro_rules!`) are not listed. A person gets one note, `thrust: 6 functions: 4 checked, 1 trusted, 1 ignored`, with a line at each function's signature.
- `all`: all of the above.

The unknowns are named after their templates: `f.pre` and `f.post` (`f.pre_x` when several parameters have one) for the contract of `f`, with their arguments in the order of the parameters and `result` last, `f.loop#k` for its `k`-th loop in the order they are written, `f.g#k r a x y` for the result `r` of its `k`-th call to `g`, related to the call's arguments (`a`) and then the other variables live there (`x`, `y`), `f.bb3.value` for another value block `bb3` makes, such as an element it indexes, and `f.bb3` for the type of a block. `old(x)` is the value the parameter `x` had on entry, where the loop also has the variable `x` or the constraint no longer has it, and `x@2` the second variable a function names `x` (a shadowing `let`). A value the program does not name is named after the stage that introduced it: `__tmp_mir_f_3` is the local `_3` of `f`'s MIR, and `__tmp_chc_c7_2` a variable of constraint `c7` that stands for no variable of the program. A variable of a constraint made where the variable of the program it held is no longer live (after a loop with a written invariant, for one) keeps that variable's name, unless the variable may no longer hold the value there: assigned again, mutably borrowed or moved out in the block, hidden by a shadowing `let`, or (a value that is not `Copy`) moved out, and not written again, on a path to the constraint. A variable bound by a quantifier, in a template (a value Thrust introduced in typing an expression) or in the solver's answer, is written `q$0`, `q$1`, …

Formulas are written as Thrust prints its constraints: `∧`, `∨`, `¬`, `==>`, `=`, `*x` and `°x` for the current and final values of a `&mut x`, `<c, f>` for a pair of them in a term, and an unknown or a user predicate applied as `p(x, y ← t)`: each argument of an unknown by the variable of the template it is, alone where the term is that variable, a `&mut` argument as its two values `*y ← c, °y ← f` (also where its term is a variable), an argument of no such variable as `_ ← t`, and a user predicate's arguments by their terms. (`←` gives an argument; `:=` is kept for a solution's interpretation of an unknown, and `=` for an equation.) A pair or a tuple equated with another is shown as its components equated, a comparison equated with `true` or `false` as the comparison or its negation, a negated comparison as the opposite one, a component of a tuple written out as that component, a boolean term compared with `true` or `false` as the condition it stands for, `x - y` compared with an integer as `x` compared with `y` moved by it, over the integers a strict bound as the bound by its neighbour (`x - y <= -1` as `x < y`, and two bounds `x < y + 1 ∧ x > y - 1` as `x = y`), `(-y) + x` as `x - y`, two bounds on a term by one value as an equation (`t > -1 ∧ t < 1` as `t = 0`), and a premise said twice once. `solution`, `inferred` and `failure` need the default `z3` solver, which is asked for a model or a refutation along with its verdict; with another solver the report says so, except that a query or a part the solver refutes is refuted once more by `z3` for its run when `z3` reads it (no forall sorts or sequences), within the solver's `THRUST_SOLVER_TIMEOUT_SECS` when that sets a limit and 30 s otherwise; the run says it is `z3`'s (in JSON, `run_by_z3`), and what `z3` answers instead of a run is said too (in JSON, `z3_answer` on the verdict line of a whole query or the part's line), a `sat` as the two solvers disagreeing. `THRUST_REPORT_FORMAT=json` writes the report as JSON lines, a `verdict` line (`sat`, `unsat`, `timeout`, `unknown` or `error`, and whether failures are refuted one per query or one per part) and then one object per part, function, failure, template and constraint, to `THRUST_REPORT_FILE` (default: standard output); each step of a failure's run carries the obligation and the span of the constraint deriving it, and each premise of a constraint or a failure is `{"text", "span"}`: an unknown applied is at the code of its template (a contract's or the entry block's at the signature, a loop's at its head, a call's result at the call), since a clause keeps no site per premise, and another premise has no span. A span the report writes names its file relative to the working directory when it is under it. In JSON a span is a range, `{"file", "line", "column", "end_line", "end_column"}`, its columns counted from 1 in characters and `end_column` after the last character, and the first line, of kind `report`, gives the format's `version` (3), the `root` directory the files are relative to and how columns count (`{"base": 1, "unit": "char", "end": "exclusive"}`). Each step of a run gives, beside the fact's text, its unknown (`pred`) and the arguments the program names (`args`); the `verdict` line gives, for an answer that is neither `sat` nor `unsat`, what the solver answered (`message`, such as `Timeout(30s)`; with `THRUST_SPLIT`, that of the first part with the crate's verdict, as `part 2: Timeout(30s)`), and so does each `part` line for its part; without `THRUST_SPLIT`, such a `verdict` line also gives the functions the query's clauses come from (`functions`, each with its span, as a `part` line does). A `function` line gives the function (`fn`), its whole `span`, what was done with its `body` (`checked`, `trusted`, `ignored`, `unselected` or `not_analyzed`), the `reason` when it was not checked, and of a checked body the `verdict` and, with `THRUST_SPLIT`, the numbers of its `parts`. `THRUST_REPORT_ONLY` limits the report to the functions it selects, written as for `THRUST_VERIFY_ONLY`. Unset, nothing is reported. The report is separate from `RUST_LOG`, whose log follows the analysis rather than the program.

## Configuration

Several environment variables are used by Thrust to configure its behavior:

- `THRUST_SOLVER`: A CHC solver command used to solve CHC constraints generated by Thrust. Default: `z3`. When `z3` reports that it cannot read a query (or a part) with forall sorts or sequences, which only PCSat reads, the error says so. Any other command is taken to read CoAR's `declare-dep-exists-fun`, and every unknown with a computed dependency set, empty or not, is declared with it; for `z3` an unknown with an empty set stays a plain `declare-fun`.
- `THRUST_SOLVER_ARGS`: Whitespace-separated command-line flags passed to the solver. The default is `fp.engine=spacer fp.spacer.global=true fp.validate=true` when the solver is `z3`.
- `THRUST_SOLVER_TIMEOUT_SECS`: Timeout for waiting on results from the solver. Default: `30`
- `THRUST_OUTPUT_DIR`: When configured, Thrust outputs intermediate smtlib2 files into this directory. The comments in the query follow the level `RUST_LOG` enables for the `thrust::chc::smtlib2` target: none by default; at `info`, what each quantified variable stands for and one line per clause and declaration with the fields that place it in the source (`span`, `def`, `def_id`, `bb`, `stmt_idx`, `term`, `type_param`); at `debug`, every field of the spans it was made in, and each clause's typing environment and where its body and head come from.
- `THRUST_NO_INJECT_STD`: When set to `1`, Thrust does not inject `std.rs` into the analyzed crate.
- `THRUST_TRY_SPECS`: When set to `1`, Thrust enables `feature(try_trait_v2)` in the analyzed crate and injects `std_try.rs`, the specifications of `Try::branch` and `FromResidual::from_residual` for `Option` and `Result` that `?` needs. On a `Result` the error is converted by `From::from`: the specification requires its precondition at the error (`pre!`) and gives its postcondition (`post!`), so a conversion between two error types takes the impl's contract, and one through an impl of another crate needs that impl specified.
- `THRUST_CANDIDATE_ATOMS`: When set to `1`, the unknown of each loop head gets candidate atoms, declared as `(set-info :candidates ...)` and never asserted: every conjunct of the enclosing function's requires and ensures, and the conjuncts over reference parameters of the contracts of the functions the loop calls, instantiated at the terms over the loop head's arguments of the matching sorts (an outermost `exists` also opened at them), and `^x = ^y` for every two `&mut` terms of one sort. When set to `2`, the loop head also gets the facts that hold where the loop is entered: the concrete conjuncts of the clauses that enter it (with the unknowns of a single defining clause unfolded), read back onto the head's arguments, an integer equality also as its two inequalities, and the facts of the head's own type (`x >= 0` of an unsigned `x`). Only a dependency-aware solver (not `z3`) is given them; PCSat reads them as qualifiers and, with its validator's `houdini_declared_atoms`, as the start of a Houdini-style check.
- `THRUST_FLAT_PRED_ARGS`: When set, a tuple, `Box` or `Mut` argument of a loop head's unknown (an unknown in the head and the body of one clause) is passed as its components, `current x` and `final x` for a `Mut`, recursively. The loop head's candidate atoms move onto the components.
- `THRUST_DEDUP_PRED_ARGS`: When set, an argument of a loop head's unknown that every clause defining it makes equal to a lower argument is removed, and each use of the unknown keeps the equality in its body; the equalities are those among the top-level conjuncts of the clause bodies and of the cases of a top-level disjunction, closed under congruence. A candidate atom reads a removed argument as the argument it equals. With `THRUST_FLAT_PRED_ARGS`, the components are compared after flattening.
- `THRUST_VERIFY_ONLY`: A comma-separated list of the parts of the crate to verify; see [Verifying part of a crate](#verifying-part-of-a-crate). Default: the whole crate.
- `THRUST_SPLIT`, `THRUST_CACHE_DIR`, `THRUST_CACHE_SALT`: Solve the constraints in parts, that many at a time, keep the verdicts in that directory, keyed also by the salt; see [Solving a crate in parts](#solving-a-crate-in-parts). Default: one query, nothing kept.
- `THRUST_REPORT`, `THRUST_REPORT_FORMAT`, `THRUST_REPORT_FILE`, `THRUST_REPORT_ONLY`: What to report of the inference, in which format, where, and for which functions; see [Reading what Thrust infers](#reading-what-thrust-infers). Default: nothing.
- `THRUST_PER_INSTANCE_GENERICS`: When set to `1`, a generic function with a body is not verified once over its type parameters; its body is analyzed at each instance a call site reaches, as upstream Thrust does, and a generic function no call site instantiates is not verified. A `Drop::drop` is still verified once over its type parameters, since code Thrust does not analyze may drop a value at an instance no call site reaches. A crate with an `Invariant` impl is analyzed so whatever the variable says ([Type invariants](#type-invariants)). For comparing the two treatments.
- `THRUST_ENUM_EXPANSION_DEPTH_LIMIT`: When Thrust works with enums, it "expands" the structure of the enum value onto its environment. This configuration value sets the limit on the depth of recursion during this expansion to handle enums that are defined recursively. It is our future work to discover a sensible value for this automatically. Default: `2`
- `THRUST_INT_RANGE`: When set to `conversions`, the range of every value of a Rust integer type is assumed (`[0, 2^w)` of a `w`-bit unsigned type, `[-2^(w-1), 2^(w-1))` of a signed one, and of each element of a sequence of `UIntN<w>` or `IntN<w>`, which the injected `std.rs` makes the model of a `w`-bit unsigned or signed type in place of `UInt` or `Int` while the option is set; and of each integer an enum value holds in the payload of its variant, through tuples and pointers but not through a recursive enum's own payloads; a variable an annotation's `forall` or `exists` binds at an integer type ranges over it, and a law's variable over all the facts of its type) and checked where an integer enters it (a cast, a checked operation, a value of a wider or unbounded type, a ghost term and the value of a logic function's definition, all of whose integers, in tuples and enum payloads too, must have the ranges of its type, and an enum value entering its type at other arguments; a ghost term or logic function of a recursive enum with such a payload is not supported; a logic function whose model arithmetic may leave its machine-integer result type's range fails its definition's check, and is written to return `Int`); the result of arithmetic is not checked, so a path on which an operation overflows is dropped. When set to `all`, `+`, `-`, `*` and negation are checked too, so an overflow is an error. Unset, only `0 <=` of an unsigned value is used, of a variable of a law as well; a variable an annotation binds then ranges over every integer.
- `THRUST_UNSPECIFIED_UNREACHABLE`: When set to `1`, a call of a function of another crate without a specification that is not on a panicking path is checked to be unreachable, with a warning, instead of stopping the analysis. For programs whose unspecified calls are unreachable, such as the coroutine case study. Default: such a call stops with `no specification`.
- `THRUST_CHECK_UINT_FACTS`: When set, the result of every unsigned addition, multiplication, division and remainder is also required non-negative where it is computed. A value of an unsigned type is otherwise assumed non-negative, and only the places that may take it out of range are checked (a subtraction without overflow checks, a ghost term, a logic function's definition, an integer that becomes an unsigned value); the mode is for checking once that no other place makes an unsigned value.

### PCSat

Thrust is developed alongside [CoAR](https://github.com/hiroshi-unno/coar), which provides the PCSat solver. Some Thrust features require PCSat. Set `THRUST_SOLVER=tests/thrust-pcsat-wrapper` to use PCSat through Docker.

## Development

The implementation of the Thrust is largely divided into the following modules.

- `analyze`: MIR analysis. Further divided into the modules corresponding to the program units: `analyze::crate_`, `analyze::local_def`, and `analyze::basic_block`. `analyze::annot` and `analyze::annot_fn` translate the lowered annotation attributes into refinement types and formulas.
- `refine`: Typing environment and related implementations.
- `rty`: Refinement type primitives.
- `chc`: CHC and logic primitives, and it also implements an invocation of the underlying CHC solver. `chc::answer` reads what the solver answers besides its verdict back into terms and formulas, the inverse of the SMT-LIB2 the query is written in.
- `report`: The report `THRUST_REPORT` asks for. It reads the templates and clauses the analysis left, the spans each was made in, and the solver's model or refutation, and arranges them by the function and loop they come from. It reads the solver's answers with `chc::answer` and prints every formula with the `chc` printer.

The surface annotation syntax (`#[thrust_macros::requires]`, `ensures`, `param`, `ret`, `sig`, `predicate`, `invariant!`, `pre!`/`post!`, …) is implemented in the `thrust-macros` crate. These procedural macros expand into a small set of internal plugin attributes — chiefly `#[thrust::formula_fn]` companion functions (written as ordinary Rust over the `thrust_models` model types) together with `#[thrust::requires_path]`, `#[thrust::ensures_path]`, and `#[thrust::refinement_path(..)]` markers that link those companions to the function being specified. `analyze::annot_fn` then reads the type-checked HIR of each `formula_fn` to build the corresponding `chc::Formula`/`rty::Refinement`. The model types themselves are declared in `std.rs`, which Thrust injects into every crate it analyzes. The bodies in the injected `std.rs`, such as the proofs of its trait laws, are not analyzed there; `tests/ui/pass/iterators/std_iterator_spec_laws.rs` checks them once by compiling `std.rs` as an ordinary source file. The spec of a std function whose body is safe code names its target with `thrust_std_target!(<std's function>(..), <transcription>(..))`: the target is std's function, and under `--cfg thrust_std_conformance` it is the transcription, a local function holding std's body, which Thrust then checks against the unchanged spec as it checks any local target; `tests/ui/pass/std_specs/option.rs` does so for `Option`'s `eq`, `branch` and `from_residual` (its query needs PCSat), and `tests/std_transcriptions.rs` checks without a solver that each transcription is the body of the std function it names in the toolchain's `rust-src`.

The implementation generates subtyping constraints in the form of CHCs (`chc::System`). The entry point is `analyze::crate_::Analyzer::run`, followed by `analyze::local_def::Analyzer::run` and `analyze::basic_block::Analyzer::run`, while accumulating the necessary information in `analyze::Analyzer`. Once `chc::System` is collected for the entire input, it invokes an external CHC solver via the `chc::solver` module and subsequently reports the result.

## Publication

Hiromi Ogawa, Taro Sekiyama, and Hiroshi Unno. Thrust: A Prophecy-based Refinement Type System for Rust. PLDI 2025.

## Acknowledgments

This work is supported by JSPS KAKENHI Grant Number [25K24739](https://kaken.nii.ac.jp/en/grant/KAKENHI-PROJECT-25K24739/).

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
