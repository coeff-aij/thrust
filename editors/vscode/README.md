# Thrust for VS Code (prototype)

Runs Thrust on the Rust file in the editor and shows its report (`THRUST_REPORT=1`,
`THRUST_REPORT_FORMAT=json`) where the code is:

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
- the verdict of the report's `verdict` line (`safe`, `unsafe`, `unknown`, or `error` for a run
  that wrote none, such as a compile error) in the status bar; clicking it opens the run's
  command and output.

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

## Settings

- `thrust.command`: the program and its leading arguments. `thrust-rustc` needs the
  toolchain's libraries, so outside `cargo run` call it through `rustup`, with the toolchain of
  `rust-toolchain.toml`:
  `["rustup", "run", "nightly-2025-09-08", "/path/to/thrust/target/debug/thrust-rustc"]`.
- `thrust.extraArgs` (default `-Awarnings -C debug-assertions=off`): arguments before the file,
  such as `--crate-type lib` for a file without `main`.
- `thrust.env`: further variables, such as `THRUST_SOLVER_TIMEOUT_SECS`.
- `thrust.split`, `thrust.cacheDir`: `THRUST_SPLIT` and `THRUST_CACHE_DIR` (relative to the
  workspace folder), to solve the parts on their own and keep their verdicts between saves.
- `thrust.verifyOnSave` (default on), `thrust.timeoutSecs` (default 300), `thrust.inlayHints`
  (default on).

The command "Thrust: Verify current file" runs it by hand. A run starts in the file's directory,
with the file's name as the last argument after `--error-format=json --out-dir <temporary
directory>`, so rustc's output files do not land next to the source.

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
The runner's tests replay the cases through `test/fake-thrust.js`. Nothing here starts VS Code;
the VS Code side (`src/extension.ts`) is only compiled.

## Limits

- One file at a time, as `thrust-rustc <file>`; there is no `cargo` integration, and results of
  another file's run replace the shown ones.
- A failing `ensures` is at the function's closing brace, where it returns, as the report's
  `failure` span gives it (rustc's error is at the signature); the annotation is related
  information.
- A premise of a constraint has no span, so only the run's facts are related information.
- Refutations and inferred contracts come only with `z3`; with PCSat only the verdicts and the
  parts are shown.
- Diagnostics and hints are not moved when the file is edited; they are replaced at the next run.
