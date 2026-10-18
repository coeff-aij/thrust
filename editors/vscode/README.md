# Thrust for VS Code (prototype)

Runs Thrust on the Rust file in the editor, or with `cargo check` on the cargo workspace it
belongs to, and shows its report (`THRUST_REPORT=1`, `THRUST_REPORT_FORMAT=json`) where the
code is:

- a refuted obligation as an error at its span, with the values where it fails, the constraint
  and its part, and as related information the annotation it checks (an `ensures`, or the
  callee's `requires` of a precondition), the written contracts the run assumes at calls, and the
  facts of the run reaching it at the code of the constraint that derived each;
- a part of the constraints without an answer (a timeout), or refuted without a refutation, at
  the first line of each of its functions, and a whole query without an answer as a warning at
  the top of the file, each with what the solver answered (`Timeout(30s)`, the part line's
  `message`);
- rustc's own errors at their spans; its `verification error` is left out, since the report
  places the same failure;
- the inferred contract of each function and invariant of each loop as an inlay hint at the end
  of its line, and in full (template, solution) on hover;
- the counterexample's facts as inlay hints on the lines of the constraints that derived them,
  each variable once with its values from the last fact back (`i = 1 ← 0`), so a loop header
  shows its iterations, and the facts in full on hover;
- the status of each function in the Testing view, as Dafny's extension shows its methods: an
  item per file or crate with the run's verdict, and under it an item per function the report
  names, passed, failed (with each refutation at its span) or errored when the run decides
  neither way (no answer, or a refutation elsewhere in its query), with the gutter icons the
  Testing view puts at each;
- the verdict of the report's `verdict` line (`safe`, `unsafe`, `unknown`, or `error` for a run
  that wrote none, such as a compile error) in the status bar, the worst of the crates' in a
  cargo workspace; clicking it opens the run's command and output.

A code lens "Verify this function" above each function, and the run button of a function's item
in the Testing view, run Thrust with `THRUST_VERIFY_ONLY` set to that function's path (`f`,
`m::f`, `m::Type::method`; an impl is named by its self type, see `src/analyze/selection.rs`), so
only its body is checked and its callees' written contracts are trusted. Such a run replaces the
diagnostics, hints and status of that function's lines only.

It reads version 2 of the report, the `version` of its first line, with columns counted as that
line's `columns` says, `{"base":1,"unit":"char","end":"exclusive"}`, and resolves the report's
files against the `root` that line gives. A report without that line, of another version or with
other columns is shown as an error and not read.

The design and the other options are in thrust-research `docs/design/editor-integration.md`.

## Install

Build Thrust (`cargo build` at the repository root), then in this directory:

```sh
npm install
npm run compile
npm test
```

Then either:

- run it from the Extension Development Host: open this directory in VS Code and press F5; or
- package and install it: `npm run package` (vsce, which needs Node 20 or later) writes `thrust-vscode-0.0.1.vsix`, which
  `code --install-extension thrust-vscode-0.0.1.vsix` (or "Extensions: Install from VSIX...")
  installs.

## Files and cargo workspaces

When the workspace folder has a `Cargo.toml` and the file is under a lib or bin target of the
workspace (`cargo metadata --no-deps`), a run is `cargo check --workspace --keep-going
--message-format=json`, and a function's run `cargo check -p <package> --lib` (or `--bin
<name>`) with `THRUST_VERIFY_ONLY`. `RUSTC` is `bin/thrust-rustc-cargo`, which runs
`thrust.command` with cargo's arguments and then `thrust.extraArgs`, as the fork's `README.md`
and `tests/cargo.rs` set `RUSTC` to `thrust-rustc`, and in addition, for each crate of the
workspace:

- writes the report to `<package>.<crate>.<crate type>.jsonl` in `target/thrust/reports`, and
  the extension reads the report of each crate cargo's messages name, with the crate's own
  diagnostics from those messages;
- writes Thrust's variables into the crate's dep-info as `env-dep` lines, as rustc does for
  `env!`, so cargo checks the crate again when `THRUST_VERIFY_ONLY` or `THRUST_SPLIT` changes.

The build goes to `target/thrust`, apart from the workspace's own builds, as Kani's
(`target/kani`) and Flux's (`target/flux`) do. Dependencies outside the workspace run without a
report. Any other file is run on its own, as `thrust-rustc <file>` from its directory, with the
file's name as the last argument after `--error-format=json --out-dir <temporary directory>`, so
rustc's output files do not land next to the source.

## Settings

- `thrust.command`: the program and its leading arguments. `thrust-rustc` needs the
  toolchain's libraries, so outside `cargo run` call it through `rustup`, with the toolchain of
  `rust-toolchain.toml`:
  `["rustup", "run", "nightly-2025-09-08", "/path/to/thrust/target/debug/thrust-rustc"]`.
- `thrust.cargoCommand` (default `["cargo"]`): the program running cargo, such as `["cargo",
  "+nightly-2025-09-08"]`.
- `thrust.extraArgs` (default `-Awarnings -C debug-assertions=off`): arguments before the file,
  such as `--crate-type lib` for a file without `main`; in a cargo workspace they follow cargo's
  arguments of each crate, so they must not name the crate type.
- `thrust.env`: further variables, such as `THRUST_SOLVER_TIMEOUT_SECS`.
- `thrust.split`, `thrust.cacheDir`: `THRUST_SPLIT` and `THRUST_CACHE_DIR` (relative to the
  workspace folder), to solve the parts on their own and keep their verdicts between saves. A
  split run lists every function in the Testing view; a run in one query only those with an
  inferred contract, a loop or a refutation.
- `thrust.verifyOnSave` (default on), `thrust.timeoutSecs` (default 300), `thrust.inlayHints`
  (default on), `thrust.codeLens` (default on).

The command "Thrust: Verify current file" runs it by hand: the file, or the cargo workspace.

## Tests

`npm test` compiles and runs the unit tests under plain `node --test`. They read outputs of real
Thrust runs with `z3`, kept in `test/fixtures/<case>/` (the report, rustc's JSON diagnostics on
standard error and the exit status) for the programs next to them: `safe`, `safe-split`
(`THRUST_SPLIT=2`, inferred contracts per part), `unsafe` (one refutation of an `ensures`),
`split` (`THRUST_SPLIT=2`, a refutation per refuted part, a loop's iterations), `unknown` (the
whole query times out), `unknown-split` (a part times out), `contracts` (an assertion relying on
a written contract), `precondition` (a refuted `requires`) and `broken` (a compile error), with
synthetic variants of them (another version or column unit, each verdict, a refuted part without
a refutation, run steps of several unknowns on one line).
`test/capture.sh <thrust-rustc command>` captures them again, writing the report's root as `.`.

`test/fixtures/cargo/workspace` is a workspace of two crates, `arith` (a library with a module,
an inherent and a trait impl, all verified) and `app` (a binary with a refuted `ensures`).
`test/capture-cargo.sh <thrust-rustc command>` captures its `cargo metadata` and, through
`bin/thrust-rustc-cargo`, cargo's messages, exit status and reports of `check` (the workspace),
`check-split` (`THRUST_SPLIT=2`) and `only` (`THRUST_VERIFY_ONLY=Pair::scale` in `arith`),
writing the workspace as `/workspace`. The tests read the crates' runs, verdicts and functions'
statuses from them, the wrapper is run with a stand-in compiler (`test/fake-rustc.js`), and the
functions of a file and their paths are read from the fixture's sources and from synthetic ones.

The runners' tests replay the cases through `test/fake-thrust.js` and `test/fake-cargo.js`.
Nothing here starts VS Code; the VS Code side (`src/extension.ts`) is only compiled.

## Limits

- Thrust writes no metadata for a crate it checked (`after_analysis` stops the compilation), so
  in a cargo workspace a crate that uses another crate of the workspace fails with `extern
  location for <crate> does not exist`, and cargo never keeps a crate fresh: every check runs
  Thrust on every crate again.
- The functions for the code lens are read from the text, not by the compiler: functions in
  function bodies or made by macros have no lens, a module file is placed by its path (`#[path]`
  is not read), a module file shared by a library and a binary in one directory is taken as the
  library's, and an impl of a type alias is named by the alias where Thrust names the type.
- A function's run checks the file as saved; Thrust also checks the bodies of the other
  functions without a written contract, but only the selected function's lines are updated.
- A failing `ensures` is at the function's signature, as the report's `failure` span and
  rustc's error give it, not at the `return` that breaks it; the annotation is related
  information.
- A premise of a constraint has no span, so only the run's facts are related information.
- Refutations and inferred contracts come only with `z3`; with PCSat only the verdicts and the
  parts are shown.
- Diagnostics and hints are not moved when the file is edited; they are replaced at the next run.
