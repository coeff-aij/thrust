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

function crates(name: string): cargo.CrateRun[] {
  const dir = path.join(fixtures, name);
  return cargo.crateRuns(fs.readFileSync(path.join(dir, "stdout.jsonl"), "utf8"), metadata, path.join(dir, "reports"));
}

function find(runs: cargo.CrateRun[], name: string): cargo.CrateRun {
  const run = runs.find((r) => r.target.name === name);
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
    ],
  );
  assert.strictEqual(cargo.reportDir(metadata), "/workspace/target/thrust/reports");
  assert.strictEqual(cargo.reportFileName(metadata.targets[0]), "arith.arith.lib.jsonl");
});

test("target of a file: its root file, a module under it, none outside", () => {
  assert.strictEqual(cargo.targetOf("/workspace/arith/src/ops.rs", metadata)?.name, "arith");
  assert.strictEqual(cargo.targetOf("/workspace/app/src/main.rs", metadata)?.kind, "bin");
  assert.strictEqual(cargo.targetOf("/workspace/build.rs", metadata), undefined);
  const both: cargo.Metadata = {
    ...metadata,
    targets: [
      { package: "p", name: "p", kind: "bin", crateType: "bin", srcPath: "/p/src/main.rs" },
      { package: "p", name: "p", kind: "lib", crateType: "lib", srcPath: "/p/src/lib.rs" },
    ],
  };
  assert.strictEqual(cargo.targetOf("/p/src/m.rs", both)?.kind, "lib");
  assert.strictEqual(cargo.targetOf("/p/src/main.rs", both)?.kind, "bin");
});

test("invocation: the workspace, or one target with THRUST_VERIFY_ONLY", () => {
  const whole = cargo.cargoInvocation(metadata, config({ split: 2, cacheDir: "/c" }), "/ext/bin/thrust-rustc-cargo");
  assert.strictEqual(whole.program, "cargo");
  assert.deepStrictEqual(whole.args, ["check", "--message-format=json", "--manifest-path", "/workspace/Cargo.toml", "--workspace", "--keep-going"]);
  assert.strictEqual(whole.cwd, "/workspace");
  assert.deepStrictEqual(whole.env, {
    RUSTC: "/ext/bin/thrust-rustc-cargo",
    RUSTC_WRAPPER: "",
    RUSTC_WORKSPACE_WRAPPER: "",
    CARGO_TARGET_DIR: "/workspace/target/thrust",
    THRUST_VSCODE_COMMAND: "rustup\x1frun\x1ftc\x1fthrust-rustc",
    THRUST_VSCODE_ARGS: "-Awarnings",
    THRUST_VSCODE_REPORT_DIR: "/workspace/target/thrust/reports",
    THRUST_REPORT: "1",
    THRUST_REPORT_FORMAT: "json",
    THRUST_SPLIT: "2",
    THRUST_CACHE_DIR: "/c",
  });
  const only = cargo.cargoInvocation(metadata, config(), "/w", { target: metadata.targets[1], selection: "shrink" });
  assert.deepStrictEqual(only.args.slice(-4), ["-p", "app", "--bin", "app"]);
  assert.strictEqual(only.env.THRUST_VERIFY_ONLY, "shrink");
  const lib = cargo.cargoInvocation(metadata, config(), "/w", { target: metadata.targets[0], selection: "inc" });
  assert.deepStrictEqual(lib.args.slice(-3), ["-p", "arith", "--lib"]);
});

function runWrapper(dir: string, env: Record<string, string>, args: string[]): { args: string[]; env: Record<string, string> } {
  const fake = path.join(here, "test", "fake-rustc.js");
  const out = execFileSync("sh", [wrapper, ...args], {
    env: {
      PATH: process.env.PATH ?? "",
      THRUST_VSCODE_COMMAND: [process.execPath, fake].join("\x1f"),
      THRUST_VSCODE_ARGS: ["-C", "debug-assertions=off"].join("\x1f"),
      THRUST_VSCODE_REPORT_DIR: path.join(dir, "reports"),
      THRUST_REPORT: "1",
      ...env,
    },
  });
  return JSON.parse(out.toString("utf8"));
}

test("wrapper: a report file per crate, Thrust's variables in its dep-info, cargo's arguments then the extra ones", () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-wrapper-"));
  try {
    fs.mkdirSync(path.join(dir, "deps"));
    fs.mkdirSync(path.join(dir, "reports"));
    const reportFile = path.join(dir, "reports", "arith.arith.lib.jsonl");
    fs.writeFileSync(reportFile, "an earlier check's report");
    const args = ["--crate-name", "arith", "src/lib.rs", "--crate-type", "lib", "--emit=dep-info,metadata", "-C", "extra-filename=-abc", "--out-dir", path.join(dir, "deps")];
    const primary = { CARGO_CRATE_NAME: "arith", CARGO_PKG_NAME: "arith", CARGO_PRIMARY_PACKAGE: "1", THRUST_VERIFY_ONLY: "ops::dec" };
    const ran = runWrapper(dir, primary, args);
    assert.deepStrictEqual(ran.args, [...args, "-C", "debug-assertions=off"]);
    assert.strictEqual(ran.env.THRUST_REPORT_FILE, reportFile);
    assert.strictEqual(fs.existsSync(reportFile), false);
    const depInfo = fs.readFileSync(path.join(dir, "deps", "arith-abc.d"), "utf8").split("\n");
    assert.ok(depInfo.includes("# env-dep:THRUST_VERIFY_ONLY=ops::dec"), depInfo.join("\n"));
    assert.ok(depInfo.includes("# env-dep:THRUST_REPORT=1"));
    assert.ok(depInfo.includes("# env-dep:THRUST_SPLIT"));
    // A dependency runs without a report; cargo's queries with its arguments only.
    const dependency = runWrapper(dir, { CARGO_CRATE_NAME: "dep", CARGO_PKG_NAME: "dep" }, ["--crate-name", "dep", "--crate-type", "lib"]);
    assert.strictEqual(dependency.env.THRUST_REPORT, undefined);
    assert.strictEqual(dependency.env.THRUST_REPORT_FILE, undefined);
    assert.deepStrictEqual(runWrapper(dir, {}, ["-vV"]).args, ["-vV", "-C", "debug-assertions=off"]);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});

test("a check of the workspace: a report per crate, the verdict and the functions of each", () => {
  const runs = crates("check");
  assert.deepStrictEqual(runs.map((r) => [r.target.name, r.compiled]).sort(), [["app", false], ["arith", true]]);
  const arith = find(runs, "arith");
  const parsed = report.parseReport(arith.report);
  assert.strictEqual(parsed.header?.root, "/workspace");
  assert.strictEqual(report.verdictOf(null, parsed, arith.diagnostics).verdict, "safe");
  assert.deepStrictEqual(
    report.functionResults(parsed).map((r) => [r.fn, r.status]),
    [["Pair::twice", "pass"], ["<Pair as Scale>::scale", "pass"], ["sextuple", "pass"]],
  );
  const app = find(runs, "app");
  const appReport = report.parseReport(app.report);
  assert.strictEqual(report.verdictOf(null, appReport, app.diagnostics).verdict, "unsafe");
  const results = report.functionResults(appReport);
  assert.deepStrictEqual(results.map((r) => [r.fn, r.status]), [["shrink", "fail"]]);
  assert.match(results[0].message, /refuted: ensures with result = 0, x = 1/);
  // The report's spans and rustc's are relative to the workspace's root.
  assert.strictEqual(results[0].span?.file, "app/src/main.rs");
  assert.ok(app.diagnostics.every((d) => d.spans.every((s) => s.file_name === "app/src/main.rs")));
});

test("a split check: every function of each crate with its part's verdict", () => {
  const runs = crates("check-split");
  const arith = report.functionResults(report.parseReport(find(runs, "arith").report));
  assert.deepStrictEqual(
    arith.map((r) => [r.fn, r.status, r.span?.line]),
    [
      ["ops::dec", "pass", 3],
      ["inc", "pass", 4],
      ["Pair::twice", "pass", 11],
      ["<Pair as Scale>::scale", "pass", 21],
      ["sextuple", "pass", 26],
    ],
  );
  const app = report.functionResults(report.parseReport(find(runs, "app").report));
  assert.deepStrictEqual(app.map((r) => [r.fn, r.status]), [["dec", "pass"], ["shrink", "fail"], ["main", "fail"]]);
});

test("a check of one function: its status from the lines it spans", () => {
  const runs = crates("only");
  assert.deepStrictEqual(runs.map((r) => r.target.name), ["arith"]);
  const parsed = report.parseReport(runs[0].report);
  const status = report.statusWithin(parsed, "arith/src/lib.rs", 21, 23);
  assert.deepStrictEqual([status?.fn, status?.status], ["<Pair as Scale>::scale", "pass"]);
});

test("run: the fake cargo's reports and messages, read per crate", async () => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-cargo-"));
  try {
    const local: cargo.Metadata = { ...metadata, workspaceRoot: dir, targetDirectory: dir };
    const fake = [process.execPath, path.join(here, "test", "fake-cargo.js"), path.join(fixtures, "check")];
    const result = await cargo.runCargo(local, config({ cargo: fake }), wrapper);
    assert.strictEqual(result.exitCode, 101, result.stderr);
    assert.deepStrictEqual(result.crates.map((c) => c.target.name).sort(), ["app", "arith"]);
    assert.match(find(result.crates, "app").report, /"kind":"failure"/);
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
});
