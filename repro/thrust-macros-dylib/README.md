# The driver can pick a stale `thrust-macros` dylib

## Symptom

`thrust_macros_path` (`src/main.rs:74-100`) locates the `thrust-macros` proc-macro dylib to
`--extern` into the compilation it drives. It checks, in order, `target/debug/libthrust_macros.{so,dylib,dll}`
and then a scan of `target/debug` for `libthrust_macros-<hash>.{so,dylib,dll}`, and repeats both
steps under `target/debug/deps`. Once more than one hashed copy exists under `deps/` -- which is
where a dependency build always lands -- the scan returns whichever one `std::fs::read_dir`
happens to yield first. That order is filesystem-dependent, not build-recency-dependent: a plain
`cargo build` that recompiles `thrust-macros` does not remove the older copy, and picking the
older one produces no error, just a driver silently linked against a `thrust-macros` build that
does not match the current `cargo build`.

## Reproduction

Verified on this branch (based on `main` db58667):

```console
$ cargo build
$ ls target/debug/deps/libthrust_macros-*.so | wc -l
1
$ cargo clippy --quiet
$ ls target/debug/deps/libthrust_macros-*.so | wc -l
2
```

`cargo clippy` compiles `thrust-macros` under its own profile and leaves its output in the same
`deps/` directory as the plain `cargo build`, under a different hash suffix; nothing evicts the
first copy. With two candidates present, `thrust_macros_path`'s scan (`src/main.rs:88-96`) returns
the first one `read_dir` lists, which is not tied to which of the two is newer. The person who
plants the second copy (whoever last ran `cargo clippy`, including a pre-commit hook that does)
and the person who is affected by the driver picking it (whoever next runs `thrust-rustc` or
`cargo test --test ui`) can be different people or different sessions, with no diagnostic linking
the two.

## Proposed fix

Not implemented on any branch. The direction under consideration: have `tests/ui.rs` obtain the
exact path from `cargo --message-format=json` and export it as `THRUST_MACROS_PATH`, read by
`thrust_macros_path` before it falls back to the scan above. That short-circuits the ambiguity for
the test harness, which already invokes `cargo` to build fixtures, while keeping the scan as the
fallback for a manual `cargo run -- <file>.rs`. Two questions are open: whether `THRUST_MACROS_PATH`
should also be documented and read by a plain `cargo build`/manual invocation (which has no
`cargo --message-format=json` step to source it from), and whether the scan should instead prefer
the newest-`mtime` candidate as a smaller change that does not need a new environment variable.

## Relation to upstream issues

Not tied to any open upstream issue. Upstream #255 (support multi-crate cargo projects) is a
different problem: it is about exporting a crate's specifications across a crate boundary so a
downstream crate can check calls into it, not about which of several locally built copies of the
`thrust-macros` proc-macro dylib the driver links against within one crate's build.
