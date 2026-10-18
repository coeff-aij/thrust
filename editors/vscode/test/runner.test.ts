// The runner: what it executes, and a run of a stand-in that replays a captured case.

import * as assert from "assert";
import * as path from "path";
import { test } from "node:test";
import { invocation, run, RunConfig } from "../src/runner";

const fixtures = path.join(__dirname, "..", "..", "test", "fixtures");
const fake = path.join(__dirname, "..", "..", "test", "fake-thrust.js");

function config(command: string[], overrides: Partial<RunConfig> = {}): RunConfig {
  return { command, extraArgs: ["-Awarnings"], env: {}, split: 0, cacheDir: "", timeoutSecs: 30, ...overrides };
}

test("invocation: the report's variables, the split and the cache, the file relative to its directory", () => {
  const inv = invocation("/work/crate/src/main.rs", config(["rustup", "run", "tc", "thrust-rustc"], { split: 4, cacheDir: "/work/cache", env: { A: "1" } }), "/tmp/s");
  assert.strictEqual(inv.program, "rustup");
  assert.deepStrictEqual(inv.args, ["run", "tc", "thrust-rustc", "-Awarnings", "--error-format=json", "--out-dir", "/tmp/s", "main.rs"]);
  assert.strictEqual(inv.cwd, "/work/crate/src");
  assert.deepStrictEqual(inv.env, {
    A: "1",
    THRUST_REPORT: "1",
    THRUST_REPORT_FORMAT: "json",
    THRUST_VERIFY_ONLY: "",
    THRUST_REPORT_FILE: path.join("/tmp/s", "report.jsonl"),
    THRUST_SPLIT: "4",
    THRUST_CACHE_DIR: "/work/cache",
  });
});

test("invocation: no split and no cache unless asked; a run of the whole selects everything", () => {
  const inv = invocation("/a/b.rs", config(["thrust-rustc"], { env: { THRUST_VERIFY_ONLY: "f" } }), "/tmp/s");
  assert.strictEqual(inv.env.THRUST_VERIFY_ONLY, "");
  assert.strictEqual(inv.env.THRUST_SPLIT, undefined);
  assert.strictEqual(inv.env.THRUST_CACHE_DIR, undefined);
});

test("run: the report file, standard error and the exit status of the run", async () => {
  const result = await run(path.join(fixtures, "unsafe.rs"), config([process.execPath, fake, path.join(fixtures, "split")]));
  assert.strictEqual(result.exitCode, 1);
  assert.strictEqual(result.timedOut, false);
  assert.match(result.report, /"kind":"part"/);
  assert.match(result.stderr, /verification error: Unsat/);
});

test("run: a missing report file reads as empty", async () => {
  const result = await run(path.join(fixtures, "broken.rs"), config([process.execPath, fake, path.join(fixtures, "broken")]));
  assert.strictEqual(result.exitCode, 1);
  assert.strictEqual(result.report, "");
});

test("run: stopped at the time limit", async () => {
  const result = await run(path.join(fixtures, "safe.rs"), config([process.execPath, "-e", "setTimeout(() => {}, 10000)", "--"], { extraArgs: [], timeoutSecs: 0.2 }));
  assert.strictEqual(result.timedOut, true);
});

test("run: a command that does not exist is an exit without status", async () => {
  const result = await run(path.join(fixtures, "safe.rs"), config(["/nonexistent/thrust-rustc"]));
  assert.strictEqual(result.exitCode, null);
  assert.match(result.stderr, /ENOENT/);
});

test("invocation: a selection sets THRUST_VERIFY_ONLY", () => {
  const inv = invocation("/a/b.rs", config(["thrust-rustc"]), "/tmp/s", "m::Pair::twice");
  assert.strictEqual(inv.env.THRUST_VERIFY_ONLY, "m::Pair::twice");
});

test("run: a run ignoring SIGTERM at the time limit is killed", async () => {
  const started = Date.now();
  const ignoring = [process.execPath, "-e", "process.on('SIGTERM', () => {}); setTimeout(() => {}, 20000)", "--"];
  const result = await run(path.join(fixtures, "safe.rs"), config(ignoring, { extraArgs: [], timeoutSecs: 0.2 }));
  assert.strictEqual(result.timedOut, true);
  assert.ok(Date.now() - started < 10000, `${Date.now() - started} ms`);
});
