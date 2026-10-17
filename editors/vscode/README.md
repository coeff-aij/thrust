# Thrust for VS Code (prototype)

Runs Thrust on the Rust file in the editor and shows its report (`THRUST_REPORT=1`,
`THRUST_REPORT_FORMAT=json`) where the code is:

- a refuted obligation as an error at its span, with the values where it fails and the
  constraint, and the facts of the run reaching it as related information at the code of the
  constraint that derived each;
- a part of the constraints without an answer (a timeout) as a warning at its functions, and a
  whole query without an answer as a warning at the top of the file;
- rustc's own errors at their spans;
- the inferred contract of each function and invariant of each loop as an inlay hint at the end
  of its line, and in full (template, solution) on hover;
- the counterexample's facts as inlay hints on the lines of the constraints that derived them, so
  a loop shows its iterations on its header line;
- the verdict of the run (`safe`, `unsafe`, `unknown`, or `error` for a failure before any
  answer) in the status bar; clicking it opens the run's command and output.

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
standard error and the exit status) for the programs next to them: `safe`, `unsafe` (one
refutation), `split` (`THRUST_SPLIT=2`, a refutation per refuted part, a loop's iterations),
`unknown` (the whole query times out), `unknown-split` (a part times out) and `broken` (a compile
error). `test/capture.sh <thrust-rustc command>` captures them again. The runner's tests replay
the cases through `test/fake-thrust.js`. Nothing here starts VS Code; the VS Code side
(`src/extension.ts`) is only compiled.

## Limits

- One file at a time, as `thrust-rustc <file>`; there is no `cargo` integration, and results of
  another file's run replace the shown ones.
- The report's spans are a start only (`file:line:column`). A diagnostic runs from there to the
  end of the line, or covers the line when the start is past its end, as for a failing `ensures`,
  whose span is after the function's closing brace.
- A whole run's verdict is read from the exit status and rustc's `verification error: ...`
  error, which has no span; the JSON report has no verdict line of its own when not split.
- A premise of a constraint has no span, so only the run's facts are related information.
- A part without an answer is placed at the functions the report has a site or a `function
  entry` constraint of; the others are not shown.
- Inferred contracts come only with `z3` and without `THRUST_SPLIT`; a split run, or PCSat,
  reports verdicts and refutations without them.
- Diagnostics and hints are not moved when the file is edited; they are replaced at the next run.
- Columns are characters as rustc counts them, which VS Code reads as UTF-16 units: a line with
  characters outside the BMP before the span is off.
