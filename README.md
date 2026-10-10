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

### Using Thrust with Cargo

Thrust can check Cargo projects that have no dependencies. External crates are not supported yet (#255).

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

## Annotation

Thrust can verify a wide range of programs without explicit annotations, but you can use `#[thrust_macros::requires(expr)]` and `#[thrust_macros::ensures(expr)]` to annotate the precondition and postcondition of a function, aiding in verification or specifying the intended behavior. Here, `expr` is an ordinary Rust expression that Thrust interprets as a logical formula. It supports the usual integer, boolean, and comparison operators, integer constants such as `u64::MAX`, calls to functions declared with `#[thrust_macros::predicate]` (Boolean) or `#[thrust_macros::logic]` (any model type, a single expression), and the model operations described below.

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

In an `ensures` expression, the special identifier `result` refers to the return value of the function. `requires` and `ensures` are independent: you can write either one on its own, and a missing one defaults to `true`.

A logic function may call itself (at its own type arguments, not through another function) when it carries `#[thrust_macros::variant(expr)]`, an integer expression over its parameters. Thrust emits the function as a `define-fun-rec` and adds clauses to the query requiring the variant to be non-negative and to decrease at each recursive call, under the conditions of the branches leading to it, so a variant that does not decrease is a verification error.

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

In a trait, a `#[thrust_macros::logic]` or `#[thrust_macros::predicate]` function may be declared without a body, and each implementation defines it with a function of the same kind. Where the trait is used through a type parameter, the function stands for every implementation (a universally quantified function in the query), so what is known of it there comes from the trait's contracts and its `#[thrust_macros::law]` functions, whose `requires`/`ensures` each implementation proves.

A lemma, declared with `#[thrust_macros::lemma]`, is a function whose `requires`/`ensures` state a fact and whose body, verified like any other, proves it. A recursive call is the induction hypothesis and needs `#[thrust_macros::variant(expr)]`: the variant must be non-negative and decrease at each recursive call, checked where the call is made. A lemma must terminate and change nothing, so it has no loop or closure, takes no `&mut`, and calls only other lemmas (without mutual recursion), itself under its variant, and functions outside the crate. `thrust_macros::proof!(lemma(args))` uses a lemma in executable code: the analysis checks the lemma's precondition there and assumes its postcondition, and the program evaluates the arguments without running the call.

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

The bodies of functions marked with `#[thrust::trusted]` are not analyzed by Thrust. Additionally, `#[thrust::callable]` is an alias for `#[thrust_macros::requires(true)]` and `#[thrust_macros::ensures(true)]`.

```rust
#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }
```

`#[thrust_macros::impl_trait_names(D, F)]` names the types of a function's argument-position `impl Trait` parameters, in order of occurrence, so that its `requires`/`ensures` can refer to them (e.g. `D::dl_of(*cx, dl)` for `cx: &impl HasDataLayout`); it may appear before or after them, and the number of names must equal the number of such parameters.

A method of a trait impl takes the trait's contract of that method: the one written on a local trait, or the one `std.rs` gives a std trait's method, such as `Iterator::next` for a type implementing `IteratorSpec`. With `#[thrust_macros::context]` on the impl, the method may carry `requires`/`ensures` of its own instead. Its body is then checked against them, a call resolved to the method uses them, and they must refine the trait's contract: the trait's precondition implies the method's, and the method's postcondition implies the trait's under the trait's precondition.

A `for` loop runs over any type implementing `IteratorSpec` (`std.rs` gives one to ranges of integers, slice and `Vec` iterators, and `Enumerate`/`Zip` of them): `into_iter` of an iterator is the identity, and each step is `Iterator::next`'s contract. A loop invariant written as `thrust_macros::invariant!` at the start of the loop body may name the iterator as `iter`. In a function under `#[thrust_macros::context]`, such an invariant may also name `iter_old`, the iterator before the loop, and `produced`, the ghost sequence of the items returned so far: the loop is desugared as Creusot does, and `produces(iter_old, produced, iter)` is conjoined to the invariant.

### Verifying part of a crate

`#![thrust::verify_only("a::b", "c::**", "d::Type::method")]` in the crate root, after `#![feature(custom_inner_attributes)]`, verifies only the selected functions and assumes the contracts of the others, so that a large crate can be verified one part at a time. Each entry is a path relative to the crate root (a leading `crate::` is allowed, and `crate` alone is the root module):

- a module selects the functions defined directly in it, not those of its submodules;
- `m::**` selects module `m` with all its submodules;
- any other path selects the named function with its closures, or every function defined inside the named item (a type's methods, a function's nested functions).

A method belongs to the module of its `impl` block and is named through the impl's self type, `module::Type::method`, for inherent and trait impls alike; a method of an impl for a type that is not a struct, enum or union is selected only through its module. Several attributes take the union of their entries.

A function outside the selection that has a written contract (`requires`/`ensures`, `#[thrust::callable]`, or the contract of the trait method it implements) is treated as `#[thrust::trusted]`. One without a contract is still analyzed, because its callers use the contract inferred from its body. A trait law that an impl outside the selection inherits is assumed there rather than checked. Predicates, logic functions and model declarations are unaffected, and so are `#[thrust::trusted]` and `#[thrust::ignored]`. Without the attribute, the whole crate is verified.

## Configuration

Several environment variables are used by Thrust to configure its behavior:

- `THRUST_SOLVER`: A CHC solver command used to solve CHC constraints generated by Thrust. Default: `z3`. Any other command is taken to read CoAR's `declare-dep-exists-fun`, and every unknown with a computed dependency set, empty or not, is declared with it; for `z3` an unknown with an empty set stays a plain `declare-fun`.
- `THRUST_SOLVER_ARGS`: Whitespace-separated command-line flags passed to the solver. The default is `fp.spacer.global=true fp.validate=true` when the solver is `z3`.
- `THRUST_SOLVER_TIMEOUT_SECS`: Timeout for waiting on results from the solver. Default: `30`
- `THRUST_OUTPUT_DIR`: When configured, Thrust outputs intermediate smtlib2 files into this directory.
- `THRUST_NO_INJECT_STD`: When set to `1`, Thrust does not inject `std.rs` into the analyzed crate.
- `THRUST_TRY_SPECS`: When set to `1`, Thrust enables `feature(try_trait_v2)` in the analyzed crate and injects `std_try.rs`, the specifications of `Try::branch` and `FromResidual::from_residual` for `Option` and `Result` that `?` needs.
- `THRUST_CANDIDATE_ATOMS`: When set to `1`, the unknown of each loop head gets candidate atoms, declared as `(set-info :candidates ...)` and never asserted: every conjunct of the enclosing function's requires and ensures, and the conjuncts over reference parameters of the contracts of the functions the loop calls, instantiated at the terms over the loop head's arguments of the matching sorts (an outermost `exists` also opened at them), and `^x = ^y` for every two `&mut` terms of one sort. When set to `2`, the loop head also gets the facts that hold where the loop is entered: the concrete conjuncts of the clauses that enter it (with the unknowns of a single defining clause unfolded), read back onto the head's arguments, an integer equality also as its two inequalities, and the facts of the head's own type (`x >= 0` of an unsigned `x`). Only a dependency-aware solver (not `z3`) is given them; PCSat reads them as qualifiers and, with its validator's `houdini_declared_atoms`, as the start of a Houdini-style check.
- `THRUST_FLAT_PRED_ARGS`: When set, a tuple, `Box` or `Mut` argument of a loop head's unknown (an unknown in the head and the body of one clause) is passed as its components, `current x` and `final x` for a `Mut`, recursively. The loop head's candidate atoms move onto the components.
- `THRUST_DEDUP_PRED_ARGS`: When set, an argument of a loop head's unknown that every clause defining it makes equal to a lower argument is removed, and each use of the unknown keeps the equality in its body; the equalities are those among the top-level conjuncts of the clause bodies and of the cases of a top-level disjunction, closed under congruence. A candidate atom reads a removed argument as the argument it equals. With `THRUST_FLAT_PRED_ARGS`, the components are compared after flattening.
- `THRUST_PER_INSTANCE_GENERICS`: When set to `1`, a generic function with a body is not verified once over its type parameters; its body is analyzed at each instance a call site reaches, as upstream Thrust does, and a generic function no call site instantiates is not verified. For comparing the two treatments.
- `THRUST_ENUM_EXPANSION_DEPTH_LIMIT`: When Thrust works with enums, it "expands" the structure of the enum value onto its environment. This configuration value sets the limit on the depth of recursion during this expansion to handle enums that are defined recursively. It is our future work to discover a sensible value for this automatically. Default: `2`
- `THRUST_INT_RANGE`: When set to `conversions`, the range of every value of a Rust integer type is assumed (`[0, 2^w)` of a `w`-bit unsigned type, `[-2^(w-1), 2^(w-1))` of a signed one, and of each element of a sequence of `UIntN<w>` or `IntN<w>`, which the injected `std.rs` makes the model of a `w`-bit unsigned or signed type in place of `UInt` or `Int` while the option is set; a variable an annotation's `forall` or `exists` or a law binds at such a type ranges over it, and so does a value a `match` takes out of an enum) and checked where an integer enters it (a cast, a checked operation, a ghost term, a value of a wider or unbounded type); the result of arithmetic is not checked, so a path on which an operation overflows is dropped. When set to `all`, `+`, `-`, `*` and negation are checked too, so an overflow is an error. Unset, only `0 <=` of an unsigned value is used.
- `THRUST_CHECK_UINT_FACTS`: When set, the result of every unsigned addition, multiplication, division and remainder is also required non-negative where it is computed. A value of an unsigned type is otherwise assumed non-negative, and only the places that may take it out of range are checked (a subtraction without overflow checks, a ghost term, an integer that becomes an unsigned value); the mode is for checking once that no other place makes an unsigned value.

### PCSat

Thrust is developed alongside [CoAR](https://github.com/hiroshi-unno/coar), which provides the PCSat solver. Some Thrust features require PCSat. Set `THRUST_SOLVER=tests/thrust-pcsat-wrapper` to use PCSat through Docker.

## Development

The implementation of the Thrust is largely divided into the following modules.

- `analyze`: MIR analysis. Further divided into the modules corresponding to the program units: `analyze::crate_`, `analyze::local_def`, and `analyze::basic_block`. `analyze::annot` and `analyze::annot_fn` translate the lowered annotation attributes into refinement types and formulas.
- `refine`: Typing environment and related implementations.
- `rty`: Refinement type primitives.
- `chc`: CHC and logic primitives, and it also implements an invocation of the underlying CHC solver.

The surface annotation syntax (`#[thrust_macros::requires]`, `ensures`, `param`, `ret`, `sig`, `predicate`, `invariant!`, `pre!`/`post!`, …) is implemented in the `thrust-macros` crate. These procedural macros expand into a small set of internal plugin attributes — chiefly `#[thrust::formula_fn]` companion functions (written as ordinary Rust over the `thrust_models` model types) together with `#[thrust::requires_path]`, `#[thrust::ensures_path]`, and `#[thrust::refinement_path(..)]` markers that link those companions to the function being specified. `analyze::annot_fn` then reads the type-checked HIR of each `formula_fn` to build the corresponding `chc::Formula`/`rty::Refinement`. The model types themselves are declared in `std.rs`, which Thrust injects into every crate it analyzes. The bodies in the injected `std.rs`, such as the proofs of its trait laws, are not analyzed there; `tests/ui/pass/iterators/std_iterator_spec_laws.rs` checks them once by compiling `std.rs` as an ordinary source file.

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
