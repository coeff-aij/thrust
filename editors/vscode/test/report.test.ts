// The parsing of real Thrust runs, captured by test/capture.sh into test/fixtures/<case>.

import * as assert from "assert";
import * as fs from "fs";
import * as path from "path";
import { test } from "node:test";
import * as report from "../src/report";

const fixtures = path.join(__dirname, "..", "..", "test", "fixtures");

interface Case {
  report: report.Report;
  diagnostics: report.RustcDiagnostic[];
  other: string[];
  exit: number;
}

function load(name: string): Case {
  const dir = path.join(fixtures, name);
  const reportFile = path.join(dir, "report.jsonl");
  const text = fs.existsSync(reportFile) ? fs.readFileSync(reportFile, "utf8") : "";
  const { diagnostics, other } = report.parseDiagnostics(fs.readFileSync(path.join(dir, "stderr.jsonl"), "utf8"));
  return { report: report.parseReport(text), diagnostics, other, exit: Number(fs.readFileSync(path.join(dir, "exit"), "utf8")) };
}

function outcome(c: Case): report.Outcome {
  return report.verdictOf(c.exit, c.report, c.diagnostics);
}

const fallback: report.Location = { file: "fallback.rs", line: 1, column: 1 };

test("parseLocation reads the last two fields as line and column", () => {
  assert.deepStrictEqual(report.parseLocation("unsafe.rs:5:2"), { file: "unsafe.rs", line: 5, column: 2 });
  assert.deepStrictEqual(report.parseLocation("C:\\src\\a.rs:10:3"), { file: "C:\\src\\a.rs", line: 10, column: 3 });
  assert.strictEqual(report.parseLocation("unsafe.rs"), undefined);
  assert.strictEqual(report.parseLocation(null), undefined);
});

test("every line of every captured report is of a known kind", () => {
  for (const name of ["safe", "unsafe", "split", "unknown", "unknown-split"]) {
    const c = load(name);
    assert.deepStrictEqual(c.report.unparsed, [], name);
    assert.deepStrictEqual(c.other, [], name);
  }
});

test("safe: verdict, no findings, inferred contract and invariant as hints", () => {
  const c = load("safe");
  assert.strictEqual(outcome(c).verdict, "safe");
  assert.deepStrictEqual(report.findings(c.report, c.diagnostics, outcome(c), fallback), []);
  const hints = report.hints(c.report);
  const contract = hints.find((h) => h.label.startsWith("inferred contract"));
  assert.ok(contract);
  assert.deepStrictEqual(contract.location, { file: "safe.rs", line: 1, column: 1 });
  assert.match(contract.tooltip, /fn add_one\(x: \{int \| x = 1\}\)/);
  assert.match(contract.tooltip, /add_one\.post x result := result = 2/);
  const invariant = hints.find((h) => h.label.startsWith("inferred invariant"));
  assert.ok(invariant);
  assert.deepStrictEqual(invariant.location, { file: "safe.rs", line: 9, column: 11 });
  // Blocks other than loop heads are not shown.
  assert.strictEqual(hints.length, 2);
});

test("unsafe: the refuted ensures with its values and the run as related information", () => {
  const c = load("unsafe");
  assert.strictEqual(outcome(c).verdict, "unsafe");
  const findings = report.findings(c.report, c.diagnostics, outcome(c), fallback);
  assert.strictEqual(findings.length, 1);
  const [failure] = findings;
  assert.deepStrictEqual(failure.location, { file: "unsafe.rs", line: 5, column: 2 });
  assert.strictEqual(failure.severity, "error");
  assert.match(failure.message, /^refuted: ensures in `withdraw`/);
  assert.match(failure.message, /where it fails: result = -1, b = 0, a = 0/);
  assert.match(failure.message, /c0: \(result = __tmp_mir_withdraw_3 - 1 ∧ .*\) ==> result = b - a/);
  assert.deepStrictEqual(failure.related, [
    {
      location: { file: "unsafe.rs", line: 3, column: 1 },
      message: "withdraw.bb0(b = 0, a = 0, old(b) = 0, old(a) = 0)   [c1 function entry]",
    },
  ]);
});

test("unsafe: the values at the failing line and each fact at its constraint's line", () => {
  const c = load("unsafe");
  const facts = report.hints(c.report).filter((h) => h.kind === "fact");
  assert.deepStrictEqual(
    facts.map((h) => [h.location.line, h.label]),
    [
      [5, "fails with result = -1, b = 0, a = 0, __tmp_mir_withdraw_3 = 0"],
      [3, "withdraw.bb0(b = 0, a = 0, old(b) = 0, old(a) = 0)"],
    ],
  );
});

test("split: every part, a refutation per refuted part, facts of a loop joined on its line", () => {
  const c = load("split");
  const o = outcome(c);
  assert.strictEqual(o.verdict, "unsafe");
  assert.strictEqual(o.detail, "3 parts: 1 sat, 2 unsat; 0 from the cache");
  assert.deepStrictEqual(
    c.report.parts.map((p) => [p.functions.join(","), p.verdict]),
    [
      ["withdraw", "unsat"],
      ["count_to", "unsat"],
      ["main", "sat"],
    ],
  );
  const findings = report.findings(c.report, c.diagnostics, o, fallback);
  assert.deepStrictEqual(
    findings.map((f) => [f.location.line, f.message.split("\n")[0]]),
    [
      [5, "refuted: ensures in `withdraw`"],
      [17, "refuted: ensures in `count_to`"],
    ],
  );
  const loop = findings[1];
  assert.match(loop.message, /where it fails: s = 2, n = 1, i = 1/);
  assert.deepStrictEqual(
    loop.related.map((r) => r.location.line),
    [12, 12, 9],
  );
  const loopLine = report.hints(c.report).find((h) => h.kind === "fact" && h.location.line === 12);
  assert.ok(loopLine);
  assert.ok(loopLine.label.startsWith("count_to.loop#1(n = 1, i = 1, s = 2, old(n) = 1)  ←  count_to.loop#1(n = 1, i = 0"));
  assert.ok(loopLine.label.length <= 100);
  assert.match(loopLine.tooltip, /\ncount_to\.loop#1\(n = 1, i = 1, s = 2, old\(n\) = 1\)\ncount_to\.loop#1\(n = 1, i = 0, s = 0, old\(n\) = 1\)$/);
});

test("unknown: a timeout of the whole query is read from rustc's error and shown at the file", () => {
  const c = load("unknown");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "unknown", detail: "Timeout(2s)" });
  const findings = report.findings(c.report, c.diagnostics, o, fallback);
  assert.deepStrictEqual(findings, [
    { location: fallback, severity: "warning", message: "Thrust: unknown (Timeout(2s))", related: [], source: "thrust" },
  ]);
  // Without a model the templates carry no solution, so nothing is inferred to show.
  assert.deepStrictEqual(report.hints(c.report), []);
});

// The report of a part without an answer has the sites of `mul` but nothing of `main`, so the
// part is shown at `mul` only.
test("unknown-split: a part that times out is shown at the entries of its functions the report places", () => {
  const c = load("unknown-split");
  const o = outcome(c);
  assert.strictEqual(o.verdict, "unknown");
  assert.strictEqual(o.detail, "1 parts: 0 sat, 0 unsat, 1 without an answer; 0 from the cache");
  const findings = report.findings(c.report, c.diagnostics, o, fallback);
  assert.deepStrictEqual(
    findings.map((f) => [f.location.line, f.severity, f.message]),
    [[1, "warning", "Thrust: timeout in the part of `main`, `mul`; no refutation"]],
  );
});

test("broken: a compile error is an error at rustc's span, without a report", () => {
  const c = load("broken");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "error", detail: "mismatched types" });
  const findings = report.findings(c.report, c.diagnostics, o, fallback);
  assert.strictEqual(findings.length, 1);
  assert.strictEqual(findings[0].source, "rustc");
  assert.deepStrictEqual(findings[0].location, { file: "broken.rs", line: 2, column: 18, endLine: 2, endColumn: 22 });
});

test("resolveLocation resolves the file against the run's directory", () => {
  const resolved = report.resolveLocation({ file: "unsafe.rs", line: 5, column: 2 }, "/work/crate");
  assert.strictEqual(resolved.file, path.resolve("/work/crate", "unsafe.rs"));
});
