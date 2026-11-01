// Cargo workspaces: the metadata, the check's invocation, the wrapper, and the crates' runs of
// real checks of test/fixtures/cargo/workspace captured by test/capture-cargo.sh.

import * as assert from "assert";
import { execFileSync } from "child_process";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { test } from "node:test";
import * as cargo from "../src/cargo";
import * as report from "../src/report";

const here = path.join(__dirname, "..", "..");
const fixtures = path.join(here, "test", "fixtures", "cargo");
const wrapper = path.join(here, "bin", "thrust-rustc-cargo");
const metadata = cargo.parseMetadata(fs.readFileSync(path.join(fixtures, "metadata.json"), "utf8"));

function config(overrides: Partial<cargo.CargoConfig> = {}): cargo.CargoConfig {
  return {
    cargo: ["cargo"],
    command: ["rustup", "run", "tc", "thrust-rustc"],
    extraArgs: ["-Awarnings"],
    env: {},
    split: 0,
    cacheDir: "",
    timeoutSecs: 30,
    ...overrides,
  };
}

function target(pkg: string, kind: string): cargo.Target {
  const found = metadata.targets.find((t) => t.package === pkg && t.kind === kind);
  assert.ok(found, `${pkg} ${kind}`);
  return found;
}

function crates(name: string, only?: cargo.Target): cargo.CrateRun[] {
  const dir = path.join(fixtures, name);
  return cargo.crateRuns(fs.readFileSync(path.join(dir, "stdout.jsonl"), "utf8"), metadata, path.join(dir, "reports"), only);
}

function find(runs: cargo.CrateRun[], name: string, kind = name === "app" ? "bin" : "lib"): cargo.CrateRun {
  const run = runs.find((r) => r.target.name === name && r.target.kind === kind);
  assert.ok(run, name);
  return run;
}

test("metadata: the workspace's lib and bin targets", () => {
  assert.strictEqual(metadata.workspaceRoot, "/workspace");
  assert.deepStrictEqual(
    metadata.targets.map((t) => [t.package, t.name, t.kind, t.crateType, t.srcPath]),
    [
      ["arith", "arith", "lib", "lib", "/workspace/arith/src/lib.rs"],
      ["app", "app", "bin", "bin", "/workspace/app/src/main.rs"],
      ["both", "both", "lib", "lib", "/workspace/both/src/lib.rs"],
      ["both", "both", "bin", "bin", "/workspace/both/src/main.rs"],
    ],
  );
  assert.strictEqual(cargo.reportDir(metadata), "/workspace/target/thrust/reports");
  assert.strictEqual(cargo.reportFileName(metadata.targets[0]), "arith.arith.lib.jsonl");
});

test("target of a file: its root file, a module under it (the library's when both share it), none outside", () => {
  assert.strictEqual(cargo.targetOf("/workspace/arith/src/ops.rs", metadata)?.name, "arith");
  assert.strictEqual(cargo.targetOf("/workspace/app/src/main.rs", metadata)?.kind, "bin");
  assert.strictEqual(cargo.targetOf("/workspace/both/src/main.rs", metadata)?.kind, "bin");
  assert.strictEqual(cargo.targetOf("/workspace/both/src/m.rs", metadata)?.kind, "lib");
  assert.strictEqual(cargo.targetOf("/workspace/build.rs", metadata), undefined);
});

test("invocation: the workspace, or one target whose crate the wrapper gives THRUST_VERIFY_ONLY", () => {
  const env = { RUST_LOG: "x", THRUST_SOLVER_TIMEOUT_SECS: "5" };
  const whole = cargo.cargoInvocation(metadata, config({ split: 2, cacheDir: "/c", env }), "/ext/bin/thrust-rustc-cargo");
  assert.strictEqual(whole.program, "cargo");
  assert.deepStrictEqual(whole.args, ["check", "--message-format=json", "--manifest-path", "/workspace/Cargo.toml", "--workspace", "--keep-going"]);
  assert.strictEqual(whole.cwd, "/workspace");
  assert.deepStrictEqual(whole.env, {
    RUST_LOG: "x",
    THRUST_SOLVER_TIMEOUT_SECS: "5",
    THRUST_REPORT: "1",
    THRUST_REPORT_FORMAT: "json",
    THRUST_VERIFY_ONLY: "",
    THRUST_SPLIT: "2",
    THRUST_CACHE_DIR: "/c",
    RUSTC: "/ext/bin/thrust-rustc-cargo",
    RUSTC_WRAPPER: "",
    RUSTC_WORKSPACE_WRAPPER: "",
    CARGO_TARGET_DIR: "/workspace/target/thrust",
    THRUST_VSCODE_COMMAND: "rustup\x1frun\x1ftc\x1fthrust-rustc",
    THRUST_VSCODE_ARGS: "-Awarnings",
    THRUST_VSCODE_THRUST_ID: cargo.commandIdentity(["rustup", "run", "tc", "thrust-rustc"], "/workspace"),
    THRUST_VSCODE_SOLVER_ID: cargo.fileIdentity("z3", "/workspace"),
    // Thrust records its own variables; the wrapper the others of thrust.env.
    THRUST_VSCODE_ENV_KEYS: "RUST_LOG",
    THRUST_VSCODE_REPORT_DIR: "/workspace/target/thrust/reports",
  });
  // Thrust writes the report to standard output only without a file.
  assert.deepStrictEqual(whole.unset, ["THRUST_REPORT_FILE"]);
  assert.throws(() => cargo.cargoInvocation(metadata, config({ env: { THRUST_REPORT_FILE: "/r" } }), "/w"), /THRUST_REPORT_FILE/);
  const bin = cargo.cargoInvocation(metadata, config(), "/w", { target: target("both", "bin"), selection: "helper" });
  assert.deepStrictEqual(bin.args.slice(-4), ["-p", "both", "--bin", "both"]);
  assert.strictEqual(bin.env.THRUST_VERIFY_ONLY, "");
  assert.strictEqual(bin.env.THRUST_VSCODE_VERIFY_ONLY, "helper");
  assert.strictEqual(bin.env.THRUST_VSCODE_VERIFY_CRATE, "both.bin");
  const lib = cargo.cargoInvocation(metadata, config(), "/w", { target: target("arith", "lib"), selection: "inc" });
  assert.deepStrictEqual(lib.args.slice(-3), ["-p", "arith", "--lib"]);
  assert.strictEqual(lib.env.THRUST_VSCODE_VERIFY_CRATE, "arith.lib");
});

test("identity of the command: its program found on PATH and its words that are paths", () => {
  const stat = fs.statSync(process.execPath);
  const id = `${process.execPath}:${stat.size}:${stat.mtimeMs}`;
  assert.strictEqual(cargo.commandIdentity(["/nonexistent/rustup", "run", "tc", process.execPath], "/"), id);
  const saved = process.env.PATH;
  process.env.PATH = path.dirname(process.execPath);
  try {
    assert.strictEqual(cargo.commandIdentity([path.basename(process.execPath), "x"], "/"), id);
  } finally {
    process.env.PATH = saved;
  }
});

test("identity of the solver: the file THRUST_SOLVER names, on PATH or against the directory", () => {
  const stat = fs.statSync(process.execPath);
  const id = `${process.execPath}:${stat.size}:${stat.mtimeMs}`;
  const dir = path.dirname(process.execPath);
  const program = path.basename(process.execPath);
  assert.strictEqual(cargo.fileIdentity(process.execPath, "/"), id);
  assert.strictEqual(cargo.fileIdentity(`./${program}`, dir), id);
  assert.strictEqual(cargo.fileIdentity("/nonexistent/z3", "/"), "");
  const saved = process.env.PATH;
  process.env.PATH = dir;
  try {
    assert.strictEqual(cargo.solverIdentity(config({ env: { THRUST_SOLVER: program } }), "/"), id);
  } finally {
    process.env.PATH = saved;
  }
});

interface WrapperRun {
  args: string[];
  env: Record<string, string>;
  kept: Record<string, string>;
  /// What the wrapper printed on standard output.
  stdout: string;
}

function runWrapper(dir: string, env: Record<string, string>, args: string[]): WrapperRun {
  const fake = path.join(here, "test", "fake-rustc.js");
  const out = path.join(dir, "fake-rustc.json");
  const stdout = execFileSync("sh", [wrapper, ...args], {
    env: {
      PATH: process.env.PATH ?? "",
      THRUST_VSCODE_COMMAND: [process.execPath, fake].join("\x1f"),
      THRUST_VSCODE_ARGS: ["-C", "debug-assertions=off"].join("\x1f"),
      THRUST_VSCODE_REPORT_DIR: path.join(dir, "reports"),
      THRUST_REPORT: "1",
      FAKE_RUSTC_OUT: out,
      ...env,
    },
  }).toString("utf8");
  return { ...JSON.parse(fs.readFileSync(out, "utf8")), stdout };
}

/// The arguments cargo gives a crate, writing its dep-info into `dir`/deps.
function crateArgs(dir: string, crate: string, crateType: string): string[] {
  const out = path.join(dir, "deps");
  return ["--crate-name", crate, "src/lib.rs", "--crate-type", crateType, "--emit=dep-info,metadata", "-C", `extra-filename=-${crateType}`, "--out-dir", out];
}

function withScratch(body: (dir: string) => void): void {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-wrapper-"));
  try {
    fs.mkdirSync(path.join(dir, "deps"));
    fs.mkdirSync(path.join(dir, "reports"));
    body(dir);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

function depInfo(dir: string, crate: string, crateType: string): string[] {
  return fs.readFileSync(path.join(dir, "deps", `${crate}-${crateType}.d`), "utf8").split("\n");
}

test("wrapper: Thrust's standard output as the crate's report, cargo's arguments then the extra ones, what Thrust does not record in the dep-info", () => {
  withScratch((dir) => {
    const reportFile = path.join(dir, "reports", "arith.arith.lib.jsonl");
    fs.writeFileSync(reportFile, "an earlier check's report");
    const args = crateArgs(dir, "arith", "lib");
    const env = {
      CARGO_CRATE_NAME: "arith",
      CARGO_PKG_NAME: "arith",
      CARGO_PRIMARY_PACKAGE: "1",
      THRUST_SPLIT: "2",
      THRUST_VSCODE_SOLVER_ID: "/usr/bin/z3:1:2",
      THRUST_VSCODE_ENV_KEYS: ["RUST_LOG", "bad-name"].join("\x1f"),
      RUST_LOG: "info",
    };
    const ran = runWrapper(dir, env, args);
    assert.deepStrictEqual(ran.args, [...args, "-C", "debug-assertions=off"]);
    assert.strictEqual(ran.stdout, "");
    assert.strictEqual(fs.readFileSync(reportFile, "utf8"), '{"kind":"report"}\n');
    // Thrust's variables pass unchanged; Thrust records them itself.
    assert.deepStrictEqual(ran.env, { THRUST_REPORT: "1", THRUST_SPLIT: "2" });
    const lines = depInfo(dir, "arith", "lib");
    for (const line of [
      "# env-dep:THRUST_VSCODE_ARGS=-C\x1fdebug-assertions=off",
      "# env-dep:THRUST_VSCODE_SOLVER_ID=/usr/bin/z3:1:2",
      "# env-dep:RUST_LOG=info",
    ]) {
      assert.ok(lines.includes(line), `${line}\n${lines.join("\n")}`);
    }
    assert.ok(!lines.some((l) => l.startsWith("# env-dep:THRUST_SPLIT") || l.startsWith("# env-dep:bad-name")), lines.join("\n"));
  });
});

test("wrapper: a dependency's report too; cargo's queries print to cargo and get the extra arguments", () => {
  withScratch((dir) => {
    const dependency = runWrapper(dir, { CARGO_CRATE_NAME: "dep", CARGO_PKG_NAME: "dep" }, crateArgs(dir, "dep", "lib"));
    assert.strictEqual(dependency.env.THRUST_REPORT, "1");
    assert.ok(fs.existsSync(path.join(dir, "reports", "dep.dep.lib.jsonl")));
    const query = runWrapper(dir, {}, ["-vV"]);
    assert.deepStrictEqual(query.args, ["-vV", "-C", "debug-assertions=off"]);
    assert.strictEqual(query.stdout, '{"kind":"report"}\n');
  });
});

test("wrapper: THRUST_VERIFY_ONLY for the selected crate only, not the package's other one", () => {
  withScratch((dir) => {
    const selection = { CARGO_PKG_NAME: "both", CARGO_PRIMARY_PACKAGE: "1", THRUST_VSCODE_VERIFY_ONLY: "helper", THRUST_VSCODE_VERIFY_CRATE: "both.bin" };
    const bin = runWrapper(dir, { ...selection, CARGO_CRATE_NAME: "both", THRUST_VERIFY_ONLY: "" }, crateArgs(dir, "both", "bin"));
    assert.strictEqual(bin.env.THRUST_VERIFY_ONLY, "helper");
    // The other crate keeps cargo's empty selection, which Thrust records as cargo has it.
    const lib = runWrapper(dir, { ...selection, CARGO_CRATE_NAME: "both", THRUST_VERIFY_ONLY: "" }, crateArgs(dir, "both", "lib"));
    assert.strictEqual(lib.env.THRUST_VERIFY_ONLY, "");
  });
});

test("a check of the workspace: a report per crate, the verdict and the functions of each; a crate using another compiles", () => {
  const runs = crates("check");
  assert.deepStrictEqual(
    runs.map((r) => [r.target.name, r.target.kind, r.compiled]).sort(),
    [["app", "bin", false], ["arith", "lib", true], ["both", "bin", true], ["both", "lib", true]],
  );
  const arith = find(runs, "arith");
  const parsed = report.parseReport(arith.report);
  assert.strictEqual(parsed.header?.root, "/workspace");
  assert.strictEqual(cargo.crateOutcome(arith, parsed).verdict, "safe");
  assert.deepStrictEqual(
    report.functionResults(parsed).map((r) => [r.fn, r.status]),
    [["inc", "pass"], ["Pair::twice", "pass"], ["<Pair as Scale>::scale", "pass"], ["sextuple", "pass"], ["ops::dec", "pass"]],
  );
  // `app` uses `arith`, whose metadata Thrust wrote as it verified; `app` is refuted.
  const app = find(runs, "app");
  const appReport = report.parseReport(app.report);
  assert.strictEqual(cargo.crateOutcome(app, appReport).verdict, "unsafe");
  const results = report.functionResults(appReport);
  assert.deepStrictEqual(results.map((r) => [r.fn, r.status]), [["dec", "unknown"], ["shrink", "fail"], ["main", "unknown"]]);
  assert.match(results[1].message, /refuted: ensures with result = 0, x = 1/);
  // The report's spans and rustc's are relative to the workspace's root.
  assert.strictEqual(results[1].span?.file, "app/src/main.rs");
  assert.ok(app.diagnostics.every((d) => d.spans.every((s) => s.file_name === "app/src/main.rs")));
});

test("a split check: every function of each crate with its part's verdict", () => {
  const runs = crates("check-split");
  const arith = report.functionResults(report.parseReport(find(runs, "arith").report));
  assert.deepStrictEqual(
    arith.map((r) => [r.fn, r.status, r.span?.line]),
    [
      ["inc", "pass", 4],
      ["Pair::twice", "pass", 11],
      ["<Pair as Scale>::scale", "pass", 21],
      ["sextuple", "pass", 26],
      ["ops::dec", "pass", 3],
    ],
  );
  const app = report.functionResults(report.parseReport(find(runs, "app").report));
  assert.deepStrictEqual(app.map((r) => [r.fn, r.status]), [["dec", "pass"], ["shrink", "fail"], ["main", "fail"]]);
});

/// The crates cargo compiled in a captured check, each with whether it found it fresh.
function freshness(name: string): [string, string, boolean][] {
  return fs
    .readFileSync(path.join(fixtures, name, "stdout.jsonl"), "utf8")
    .split("\n")
    .filter((l) => l.includes('"reason":"compiler-artifact"'))
    .map((l) => JSON.parse(l) as { target: { name: string; kind: string[] }; fresh: boolean })
    .map((m): [string, string, boolean] => [m.target.name, m.target.kind[0], m.fresh])
    .sort();
}

test("a second check: the crates that passed are fresh and keep their reports", () => {
  assert.deepStrictEqual(freshness("check-again"), [["arith", "lib", true], ["both", "bin", true], ["both", "lib", true]]);
  const runs = crates("check-again");
  assert.deepStrictEqual(
    report.functionResults(report.parseReport(find(runs, "arith").report)).map((r) => r.status),
    ["pass", "pass", "pass", "pass", "pass"],
  );
  // The refuted crate wrote no metadata, so it is checked again.
  assert.strictEqual(cargo.crateOutcome(find(runs, "app"), report.parseReport(find(runs, "app").report)).verdict, "unsafe");
});

test("a check after runs of one function: only the crates checked under a selection run again", () => {
  // `only` selected in arith's library, `only-bin` in both's binary; both's library kept cargo's
  // empty selection, so it stays fresh.
  assert.deepStrictEqual(freshness("check-after-only"), [["arith", "lib", false], ["both", "bin", false], ["both", "lib", true]]);
});

test("a check of one function: its status from the lines it spans, the reports of the other crates not read", () => {
  const runs = crates("only", target("arith", "lib"));
  assert.deepStrictEqual(runs.map((r) => r.target.name), ["arith"]);
  const parsed = report.parseReport(runs[0].report);
  const status = report.statusWithin(parsed, "arith/src/lib.rs", { name: "scale", line: 21, fnLine: 21, endLine: 23 });
  assert.deepStrictEqual([status?.fn, status?.status], ["<Pair as Scale>::scale", "pass"]);
  // Of the whole workspace's messages, only the checked target's report is read.
  const scoped = crates("check", target("arith", "lib"));
  assert.ok(find(scoped, "arith").report.length > 0);
  assert.strictEqual(find(scoped, "app").report, "");
});

test("a check of a binary's function: the package's library checked whole, without an error", () => {
  const bin = target("both", "bin");
  const runs = crates("only-bin", bin);
  assert.deepStrictEqual(runs.map((r) => [r.target.kind, r.compiled, r.diagnostics.length]).sort(), [["bin", true, 0], ["lib", true, 0]]);
  const binRun = runs.find((r) => r.target === bin);
  assert.ok(binRun);
  const status = report.statusWithin(report.parseReport(binRun.report), "both/src/main.rs", { name: "helper", line: 1, fnLine: 1, endLine: 3 });
  assert.deepStrictEqual([status?.fn, status?.status], ["helper", "pass"]);
});

test("crate outcome: a crate cargo did not compile for an error other than a refutation is an error, whatever its report", () => {
  const arith = find(crates("check"), "arith");
  const selectsNothing: report.RustcDiagnostic = { message: "`THRUST_VERIFY_ONLY` entry `f` selects no function", level: "error", spans: [], children: [] };
  const failed = { ...arith, compiled: false, diagnostics: [selectsNothing] };
  assert.deepStrictEqual(cargo.crateOutcome(failed, report.parseReport(arith.report)), { verdict: "error", detail: selectsNothing.message });
  // A refuted crate is not compiled either, and stays unsafe.
  const app = find(crates("check"), "app");
  assert.strictEqual(cargo.crateOutcome(app, report.parseReport(app.report)).verdict, "unsafe");
});

test("run: the fake cargo's reports and messages, read per crate", async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-cargo-"));
  try {
    const local: cargo.Metadata = { ...metadata, workspaceRoot: dir, targetDirectory: dir };
    const fake = [process.execPath, path.join(here, "test", "fake-cargo.js"), path.join(fixtures, "check")];
    const result = await cargo.runCargo(local, config({ cargo: fake }), wrapper);
    assert.strictEqual(result.exitCode, 101, result.stderr);
    assert.deepStrictEqual(result.crates.map((c) => `${c.target.name} ${c.target.kind}`).sort(), ["app bin", "arith lib", "both bin", "both lib"]);
    assert.match(find(result.crates, "app").report, /"kind":"failure"/);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test("crate outcome: a crate not compiled whose report is sat is an error", () => {
  const arith = find(crates("check"), "arith");
  const outcome = cargo.crateOutcome({ ...arith, compiled: false }, report.parseReport(arith.report));
  assert.deepStrictEqual(outcome.verdict, "error");
  assert.match(outcome.detail, /did not compile the crate, though its report is sat/);
});

test("crate runs: a build script's error is a run of its own; targets are told apart by their package", () => {
  const buildScript = { kind: ["custom-build"], crate_types: ["bin"], name: "build-script-build", src_path: "/workspace/app/build.rs" };
  const message = { message: "a build script's error", level: "error", spans: [], children: [] };
  const other = { kind: ["bin"], crate_types: ["bin"], name: "app", src_path: "/elsewhere/src/main.rs" };
  const stdout = [
    { reason: "compiler-message", manifest_path: "/workspace/app/Cargo.toml", target: buildScript, message },
    { reason: "compiler-artifact", manifest_path: "/elsewhere/Cargo.toml", target: other },
  ].map((m) => JSON.stringify(m)).join("\n");
  const runs = cargo.crateRuns(stdout, metadata, "/nonexistent");
  assert.deepStrictEqual(
    runs.map((r) => [r.target.package, r.target.kind, r.target.manifestPath, r.diagnostics.length]),
    [["app", "custom-build", "/workspace/app/Cargo.toml", 1], ["app", "bin", "/elsewhere/Cargo.toml", 0]],
  );
  assert.notStrictEqual(cargo.targetKey(runs[1].target), cargo.targetKey(target("app", "bin")));
});

test("wrapper: the dep-info records the values cargo ran it with", () => {
  withScratch((dir) => {
    const env = { CARGO_CRATE_NAME: "dep", CARGO_PKG_NAME: "dep", THRUST_VSCODE_ENV_KEYS: "MY_FLAG" };
    runWrapper(dir, env, crateArgs(dir, "dep", "lib"));
    const lines = depInfo(dir, "dep", "lib");
    assert.ok(lines.includes("# env-dep:MY_FLAG"), lines.join("\n"));
    assert.ok(lines.includes("# env-dep:THRUST_VSCODE_ENV_KEYS=MY_FLAG"), lines.join("\n"));
  });
});

test("wrapper: the environment it passes on keeps variables named as its own would be", () => {
  withScratch((dir) => {
    const names = { name: "n", crate: "c", status: "s", report: "r", sep: "x" };
    const ran = runWrapper(dir, { CARGO_CRATE_NAME: "arith", CARGO_PKG_NAME: "arith", CARGO_PRIMARY_PACKAGE: "1", ...names }, crateArgs(dir, "arith", "lib"));
    assert.deepStrictEqual(ran.kept, names);
  });
});

/// The awk and sed implementations installed here, each as a directory to put first on PATH.
function toolSets(dir: string): string[] {
  const awks = ["/usr/bin/mawk", "/usr/bin/gawk", "/usr/bin/original-awk", "/usr/bin/busybox"].filter((f) => fs.existsSync(f));
  const seds = ["/bin/sed", "/usr/bin/busybox"].filter((f) => fs.existsSync(f));
  return awks.flatMap((awk) =>
    seds.map((sed) => {
      const set = path.join(dir, `${path.basename(awk)}-${path.basename(sed)}`);
      fs.mkdirSync(set);
      fs.symlinkSync(awk, path.join(set, "awk"));
      fs.symlinkSync(sed, path.join(set, "sed"));
      return set;
    }),
  );
}

test("wrapper: env-dep values escaped as rustc escapes them, with each awk and sed installed", () => {
  withScratch((dir) => {
    const sets = toolSets(dir);
    assert.ok(sets.length > 0);
    for (const set of sets) {
      const env = { CARGO_CRATE_NAME: "arith", CARGO_PKG_NAME: "arith", THRUST_VSCODE_ENV_KEYS: "MY_ARGS", MY_ARGS: "a\\b\nc\rd\n", PATH: `${set}:${process.env.PATH}` };
      runWrapper(dir, env, crateArgs(dir, "arith", "lib"));
      const lines = depInfo(dir, "arith", "lib");
      assert.ok(lines.includes("# env-dep:MY_ARGS=a\\\\b\\nc\\rd\\n"), `${set}\n${lines.join("\n")}`);
      fs.rmSync(path.join(dir, "deps", "arith-lib.d"));
    }
  });
});
