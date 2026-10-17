// The parsing of real Thrust runs, captured by test/capture.sh into test/fixtures/<case>.

import * as assert from "assert";
import * as fs from "fs";
import * as path from "path";
import { test } from "node:test";
import * as report from "../src/report";

const fixtures = path.join(__dirname, "..", "..", "test", "fixtures");
const cases = ["safe", "safe-split", "unsafe", "split", "unknown", "unknown-split", "contracts", "precondition"];

interface Case {
  text: string;
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
  return { text, report: report.parseReport(text), diagnostics, other, exit: Number(fs.readFileSync(path.join(dir, "exit"), "utf8")) };
}

function outcome(c: Case): report.Outcome {
  return report.verdictOf(c.exit, c.report, c.diagnostics);
}

function findingsOf(c: Case): report.Finding[] {
  return report.findings(c.report, c.diagnostics, outcome(c), fallback);
}

const fallback: report.Location = { file: "fallback.rs", line: 1, column: 1 };

test("every line of every captured report is of a known kind, after a header of version 1", () => {
  for (const name of cases) {
    const c = load(name);
    assert.deepStrictEqual(c.report.unparsed, [], name);
    assert.deepStrictEqual(c.other, [], name);
    assert.deepStrictEqual(c.report.header, { kind: "report", version: 1, root: ".", columns: "1-based, in characters; end_column after the last" }, name);
    assert.ok(c.report.verdict, name);
  }
});

test("a report without a header or of another version is refused", () => {
  const unsafe = load("unsafe").text.split("\n");
  const headless = report.parseReport(unsafe.slice(1).join("\n"));
  assert.match(report.refusal(headless) ?? "", /no header line/);
  const o = report.verdictOf(1, headless, []);
  assert.strictEqual(o.verdict, "error");
  assert.deepStrictEqual(report.findings(headless, [], o, fallback).map((f) => f.location), [fallback]);
  assert.deepStrictEqual(report.hints(headless), []);
  const newer = report.parseReport([unsafe[0].replace('"version":1', '"version":2'), ...unsafe.slice(1)].join("\n"));
  assert.match(report.verdictOf(1, newer, []).detail, /version 2; this extension reads version 1/);
  // No report at all (the run stopped before writing one) is not a refusal.
  assert.strictEqual(report.refusal(report.parseReport("")), undefined);
});

test("the verdict line decides the verdict, whatever the exit status", () => {
  const header = load("safe").text.split("\n")[0];
  const verdict = (v: string) => report.verdictOf(0, report.parseReport(`${header}\n{"kind":"verdict","verdict":"${v}","refutations":"one per query"}`), []).verdict;
  assert.deepStrictEqual(["sat", "unsat", "timeout", "unknown", "error"].map(verdict), ["safe", "unsafe", "unknown", "unknown", "error"]);
  // A header without a verdict: the run stopped after the report began.
  assert.deepStrictEqual(report.verdictOf(101, report.parseReport(header), []), { verdict: "error", detail: "no verdict in the report, exit status 101" });
});

test("locationOf: a range keeps its end, a zero-width span its start only", () => {
  assert.deepStrictEqual(report.locationOf({ file: "a.rs", line: 2, column: 26, end_line: 2, end_column: 41 }), {
    file: "a.rs",
    line: 2,
    column: 26,
    endLine: 2,
    endColumn: 41,
  });
  assert.deepStrictEqual(report.locationOf({ file: "a.rs", line: 5, column: 2, end_line: 5, end_column: 2 }), { file: "a.rs", line: 5, column: 2 });
  assert.strictEqual(report.locationOf(null), undefined);
});

test("utf16Column counts a character outside the BMP as two units", () => {
  assert.strictEqual(report.utf16Column("let x = 1;", 5), 5);
  assert.strictEqual(report.utf16Column('let s = "𝔸"; x', 14), 15);
  assert.strictEqual(report.utf16Column("ab", 10), 3);
});

test("safe: verdict, no findings, inferred contract and invariant as hints", () => {
  const c = load("safe");
  assert.deepStrictEqual(outcome(c), { verdict: "safe", detail: "the solver answered sat" });
  assert.deepStrictEqual(findingsOf(c), []);
  const hints = report.hints(c.report);
  const contract = hints.find((h) => h.label.startsWith("inferred contract"));
  assert.ok(contract);
  assert.deepStrictEqual(contract.location, { file: "safe.rs", line: 1, column: 1 });
  assert.match(contract.tooltip, /fn add_one\(x: \{int \| x = 1\}\)/);
  const invariant = hints.find((h) => h.label.startsWith("inferred invariant"));
  assert.ok(invariant);
  assert.deepStrictEqual(invariant.location, { file: "safe.rs", line: 9, column: 11 });
  assert.strictEqual(hints.length, 2);
});

test("safe-split: the parts' verdicts, and the same inferred contract and invariant as unsplit", () => {
  const c = load("safe-split");
  assert.deepStrictEqual(outcome(c), { verdict: "safe", detail: "2 parts: 2 sat, 0 unsat; 0 from the cache" });
  assert.deepStrictEqual(findingsOf(c), []);
  assert.deepStrictEqual(report.hints(c.report), report.hints(load("safe").report));
});

test("unsafe: the refuted ensures with its values, its annotation and the run as related information", () => {
  const c = load("unsafe");
  assert.deepStrictEqual(outcome(c), { verdict: "unsafe", detail: "refuted, one per query; other obligations may fail too" });
  // rustc's `verification error` is the same failure: only the report's is shown.
  const findings = findingsOf(c);
  assert.strictEqual(findings.length, 1);
  const [failure] = findings;
  assert.deepStrictEqual(failure.location, { file: "unsafe.rs", line: 5, column: 2 });
  assert.strictEqual(failure.severity, "error");
  assert.match(failure.message, /^refuted: ensures in `withdraw`\n/);
  assert.match(failure.message, /where it fails: result = -1, b = 0, a = 0/);
  assert.match(failure.message, /c0: \(result = __tmp_mir_withdraw_3 - 1 ∧ .*\) ==> result = b - a/);
  assert.deepStrictEqual(failure.related, [
    { location: { file: "unsafe.rs", line: 2, column: 26, endLine: 2, endColumn: 41 }, message: "the annotation it checks" },
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

test("split: every part, a refutation per refuted part named by its part, facts of a loop joined on its line", () => {
  const c = load("split");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "unsafe", detail: "3 parts: 1 sat, 2 unsat; 0 from the cache" });
  assert.strictEqual(c.report.verdict?.refutations, "one per part");
  assert.deepStrictEqual(
    c.report.parts.map((p) => [p.id, p.functions.map((f) => `${f.fn}@${f.span.line}-${f.span.end_line}`).join(","), p.verdict]),
    [
      [0, "withdraw@3-5", "unsat"],
      [1, "count_to@9-17", "unsat"],
      [2, "main@19-24", "sat"],
    ],
  );
  const findings = findingsOf(c);
  assert.deepStrictEqual(
    findings.map((f) => [f.location.line, f.message.split("\n")[0]]),
    [
      [5, "refuted: ensures in `withdraw`, part 0 (`withdraw`)"],
      [17, "refuted: ensures in `count_to`, part 1 (`count_to`)"],
    ],
  );
  const loop = findings[1];
  assert.match(loop.message, /where it fails: s = 2, n = 1, i = 1/);
  assert.deepStrictEqual(
    loop.related.map((r) => [r.location.line, r.message.split("   ")[1] ?? r.message]),
    [
      [8, "the annotation it checks"],
      [12, "[c4 loop preservation]"],
      [12, "[c2 loop entry]"],
      [9, "[c5 function entry]"],
    ],
  );
  const loopLine = report.hints(c.report).find((h) => h.kind === "fact" && h.location.line === 12);
  assert.ok(loopLine);
  assert.ok(loopLine.label.startsWith("count_to.loop#1(n = 1, i = 1, s = 2, old(n) = 1)  ←  count_to.loop#1(n = 1, i = 0"));
  assert.ok(loopLine.label.length <= 100);
  assert.match(loopLine.tooltip, /\ncount_to\.loop#1\(n = 1, i = 1, s = 2, old\(n\) = 1\)\ncount_to\.loop#1\(n = 1, i = 0, s = 0, old\(n\) = 1\)$/);
});

test("split: a refuted part without a refutation is an error at its functions", () => {
  const c = load("split");
  const withoutFirst = { ...c.report, failures: c.report.failures.filter((f) => f.part !== 0) };
  const findings = report.findings(withoutFirst, c.diagnostics, outcome(c), fallback);
  assert.deepStrictEqual(
    findings.map((f) => [f.location, f.severity, f.message.split("\n")[0]]),
    [
      [{ file: "unsafe.rs", line: 17, column: 2 }, "error", "refuted: ensures in `count_to`, part 1 (`count_to`)"],
      [{ file: "unsafe.rs", line: 3, column: 1 }, "error", "Thrust: unsat in part 0 (`withdraw`); no refutation"],
    ],
  );
});

test("unknown: a timeout of the whole query is read from the verdict line and shown at the file", () => {
  const c = load("unknown");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "unknown", detail: "the solver answered timeout" });
  assert.deepStrictEqual(findingsOf(c), [
    { location: fallback, severity: "warning", message: "Thrust: unknown (the solver answered timeout)", related: [], source: "thrust" },
  ]);
  assert.deepStrictEqual(report.hints(c.report), []);
});

test("unknown-split: a part that times out is shown at the start of each of its functions", () => {
  const c = load("unknown-split");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "unknown", detail: "1 parts: 0 sat, 0 unsat, 1 without an answer; 0 from the cache" });
  assert.deepStrictEqual(
    findingsOf(c).map((f) => [f.location, f.severity, f.message]),
    [
      [{ file: "unknown.rs", line: 1, column: 1 }, "warning", "Thrust: timeout in part 0 (`mul`, `main`); no refutation"],
      [{ file: "unknown.rs", line: 11, column: 1 }, "warning", "Thrust: timeout in part 0 (`mul`, `main`); no refutation"],
    ],
  );
});

test("contracts: a refuted assertion over a call names the written contract it assumes", () => {
  const c = load("contracts");
  const [failure, ...rest] = findingsOf(c);
  assert.deepStrictEqual(rest, []);
  assert.deepStrictEqual(failure.location, { file: "contracts.rs", line: 9, column: 5, endLine: 9, endColumn: 20 });
  assert.match(failure.message, /^refuted: assertion in `main`\nwhere it fails: y = 3\n/);
  assert.deepStrictEqual(failure.related, [
    { location: { file: "contracts.rs", line: 2, column: 26, endLine: 2, endColumn: 37 }, message: "it assumes the written contract of `grow`" },
    { location: { file: "contracts.rs", line: 8, column: 13 }, message: "main.grow#1(y = 3)   [c3 after call to `grow`]" },
  ]);
});

test("precondition: a refuted requires at the call, with the callee's annotation", () => {
  const c = load("precondition");
  const [failure, ...rest] = findingsOf(c);
  assert.deepStrictEqual(rest, []);
  assert.deepStrictEqual(failure.location, { file: "precondition.rs", line: 8, column: 13, endLine: 8, endColumn: 21 });
  assert.strictEqual(failure.message, "refuted: precondition of `grow` in `main`\nc2: -1 >= 0");
  assert.deepStrictEqual(failure.related, [
    { location: { file: "precondition.rs", line: 1, column: 27, endLine: 1, endColumn: 33 }, message: "the annotation it checks" },
  ]);
});

test("broken: a compile error is an error at rustc's span, without a report", () => {
  const c = load("broken");
  assert.strictEqual(c.text, "");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "error", detail: "mismatched types" });
  const findings = findingsOf(c);
  assert.strictEqual(findings.length, 1);
  assert.strictEqual(findings[0].source, "rustc");
  assert.deepStrictEqual(findings[0].location, { file: "broken.rs", line: 2, column: 18, endLine: 2, endColumn: 22 });
});

test("resolveFinding resolves Thrust's files against the report's root and rustc's against the run's directory", () => {
  const root = report.reportRoot(load("unsafe").report, "/work/crate");
  assert.strictEqual(root, path.resolve("/work/crate"));
  const [failure] = findingsOf(load("unsafe"));
  const resolved = report.resolveFinding(failure, "/root", "/cwd");
  assert.strictEqual(resolved.location.file, path.resolve("/root", "unsafe.rs"));
  assert.deepStrictEqual(
    resolved.related.map((r) => r.location.file),
    [path.resolve("/root", "unsafe.rs"), path.resolve("/root", "unsafe.rs")],
  );
  const [rustc] = findingsOf(load("broken"));
  assert.strictEqual(report.resolveFinding(rustc, "/root", "/cwd").location.file, path.resolve("/cwd", "broken.rs"));
});
