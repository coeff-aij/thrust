// The parsing of real Thrust runs, captured by test/capture.sh into test/fixtures/<case>.

import * as assert from "assert";
import * as fs from "fs";
import * as path from "path";
import { test } from "node:test";
import * as report from "../src/report";

const fixtures = path.join(__dirname, "..", "..", "test", "fixtures");
const cases = [
  "safe", "safe-split", "unsafe", "split", "unknown", "unknown-split", "contracts", "precondition",
  "only-main", "only-main-split", "only-trusted", "only-trusted-split", "only-twin-split",
  "only-nested", "only-nested-split",
];

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

test("every line of every captured report is of a known kind, after a header of version 2", () => {
  for (const name of cases) {
    const c = load(name);
    assert.deepStrictEqual(c.report.unparsed, [], name);
    assert.deepStrictEqual(c.other, [], name);
    assert.deepStrictEqual(c.report.header, { kind: "report", version: 2, root: ".", columns: { base: 1, unit: "char", end: "exclusive" } }, name);
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
  const older = report.parseReport([unsafe[0].replace('"version":2', '"version":1'), ...unsafe.slice(1)].join("\n"));
  assert.match(report.verdictOf(1, older, []).detail, /version 1; this extension reads version 2/);
  // Columns counted otherwise than the extension counts them.
  const utf8 = report.parseReport([unsafe[0].replace('"unit":"char"', '"unit":"utf-8"'), ...unsafe.slice(1)].join("\n"));
  assert.match(report.verdictOf(1, utf8, []).detail, /counts columns as \{"base":1,"unit":"utf-8","end":"exclusive"\}/);
  assert.deepStrictEqual(report.hints(utf8), []);
  // No report at all (the run stopped before writing one) is not a refusal.
  assert.strictEqual(report.refusal(report.parseReport("")), undefined);
});

test("the verdict line decides the verdict, whatever the exit status", () => {
  const header = load("safe").text.split("\n")[0];
  const verdict = (v: string) =>
    report.verdictOf(0, report.parseReport(`${header}\n{"kind":"verdict","verdict":"${v}","refutations":"one per query","message":null}`), []).verdict;
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
  // A refuted `ensures` is at the function's signature, as rustc's error is.
  assert.deepStrictEqual(failure.location, { file: "unsafe.rs", line: 3, column: 1, endLine: 3, endColumn: 35 });
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

test("unsafe: the values at the failing line and each fact at its constraint's line, one hint per line", () => {
  const c = load("unsafe");
  const facts = report.hints(c.report).filter((h) => h.kind === "fact");
  assert.deepStrictEqual(
    facts.map((h) => [h.location.line, h.label]),
    [
      [3, "fails with result = -1, b = 0, a = 0, __tmp_mir_withdraw_3 = 0; b = 0, a = 0, old(b) = 0, old(a) = 0"],
    ],
  );
});

test("split: every part, a refutation per refuted part named by its part, a loop's iterations per variable on its line", () => {
  const c = load("split");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "unsafe", detail: "3 parts: 1 sat, 2 unsat; 0 from the cache" });
  assert.strictEqual(c.report.verdict?.refutations, "one per part");
  assert.deepStrictEqual(
    c.report.parts.map((p) => [p.id, p.functions.map((f) => `${f.fn}@${f.span.line}-${f.span.end_line}`).join(","), p.verdict]),
    [
      [1, "withdraw@3-5", "unsat"],
      [2, "count_to@9-17", "unsat"],
      [3, "main@19-24", "sat"],
    ],
  );
  const findings = findingsOf(c);
  assert.deepStrictEqual(
    findings.map((f) => [f.location.line, f.message.split("\n")[0]]),
    [
      [3, "refuted: ensures in `withdraw`, part 1 (`withdraw`)"],
      [9, "refuted: ensures in `count_to`, part 2 (`count_to`)"],
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
  // Each variable once, with its values from the last iteration back to the entry.
  assert.strictEqual(loopLine.label, "n = 1, i = 1 ← 0, s = 2 ← 0, old(n) = 1");
  assert.match(loopLine.tooltip, /\ncount_to\.loop#1\(n = 1, i = 1, s = 2, old\(n\) = 1\)\ncount_to\.loop#1\(n = 1, i = 0, s = 0, old\(n\) = 1\)$/);
});

test("split: a refuted part without a refutation is an error at its functions", () => {
  const c = load("split");
  const withoutFirst = { ...c.report, failures: c.report.failures.filter((f) => f.part !== 1) };
  const findings = report.findings(withoutFirst, c.diagnostics, outcome(c), fallback);
  assert.deepStrictEqual(
    findings.map((f) => [f.location, f.severity, f.message.split("\n")[0]]),
    [
      [{ file: "unsafe.rs", line: 9, column: 1, endLine: 9, endColumn: 27 }, "error", "refuted: ensures in `count_to`, part 2 (`count_to`)"],
      [{ file: "unsafe.rs", line: 3, column: 1 }, "error", "Thrust: unsat in part 1 (`withdraw`); no refutation"],
    ],
  );
});

test("unknown: a timeout of the whole query is read from the verdict line, with the solver's message, and shown at the file", () => {
  const c = load("unknown");
  assert.strictEqual(c.report.verdict?.message, "Timeout(2s)");
  const o = outcome(c);
  assert.deepStrictEqual(o, { verdict: "unknown", detail: "the solver answered Timeout(2s)" });
  assert.deepStrictEqual(findingsOf(c), [
    { location: fallback, severity: "warning", message: "Thrust: unknown (the solver answered Timeout(2s))", related: [], source: "thrust" },
  ]);
  assert.deepStrictEqual(report.hints(c.report), []);
});

test("unknown-split: a part that times out is shown at the start of each of its functions", () => {
  const c = load("unknown-split");
  const o = outcome(c);
  assert.strictEqual(c.report.verdict?.message, "part 1: Timeout(2s)");
  assert.deepStrictEqual(o, { verdict: "unknown", detail: "1 part: 0 sat, 0 unsat, 1 without an answer (part 1: Timeout(2s)); 0 from the cache" });
  assert.deepStrictEqual(
    findingsOf(c).map((f) => [f.location, f.severity, f.message]),
    [
      [{ file: "unknown.rs", line: 1, column: 1 }, "warning", "Thrust: Timeout(2s) in part 1 (`mul`, `main`); no refutation"],
      [{ file: "unknown.rs", line: 11, column: 1 }, "warning", "Thrust: Timeout(2s) in part 1 (`mul`, `main`); no refutation"],
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

test("hints: the steps of one line grouped by unknown, a step without named arguments as its fact", () => {
  const span = { file: "a.rs", line: 4, column: 1, end_line: 4, end_column: 9 };
  const step = (pred: string, args: [string, string][], fact: string): report.Step => ({
    depth: 0,
    fact,
    via: "c1",
    obligation: "function entry",
    span,
    pred,
    args: args.map(([name, value]) => ({ name, value })),
  });
  const failure: report.Failure = {
    part: null,
    constraint: "c0",
    fn: "main",
    span: null,
    obligation: "assertion",
    premises: [],
    conclusion: "false",
    run: [
      step("main.price#1", [["p", "100"]], "main.price#1(p = 100)"),
      step("price.pre", [["units", "10"]], "price.pre(units = 10)"),
      step("main.bb0", [], "main.bb0"),
    ],
    truncated: false,
    values: [],
    inferred: [],
    annotation: [],
    assumes: [],
  };
  const parsed: report.Report = { ...load("unsafe").report, failures: [failure], sites: [] };
  const [hint, ...rest] = report.hints(parsed);
  assert.deepStrictEqual(rest, []);
  assert.strictEqual(hint.label, "p = 100; units = 10; main.bb0");
  assert.match(hint.tooltip, /\nmain\.price#1\(p = 100\)\nprice\.pre\(units = 10\)\nmain\.bb0$/);
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

function at(name: string, line: number, fnLine: number, endLine: number): report.FnLines {
  return { name, line, fnLine, endLine };
}

function results(name: string): [string, report.Status, number | undefined][] {
  return report.functionResults(load(name).report).map((r) => [r.fn, r.status, r.span?.line]);
}

test("functions of a split run: each with its part's verdict, a refuted one at its refutation", () => {
  assert.deepStrictEqual(results("split"), [
    ["withdraw", "fail", 3],
    ["count_to", "fail", 9],
    ["main", "pass", 19],
  ]);
  assert.deepStrictEqual(results("safe-split"), [
    ["add_one", "pass", 1],
    ["main", "pass", 15],
    ["count_to", "pass", 7],
  ]);
  const timedOut = report.functionResults(load("unknown-split").report);
  assert.deepStrictEqual(timedOut.map((r) => [r.fn, r.status]), [["mul", "unknown"], ["main", "unknown"]]);
  assert.match(timedOut[0].message, /Timeout\(2s\)/);
});

test("functions of a run in one query: those it names, a refuted one failing", () => {
  assert.deepStrictEqual(results("safe"), [
    ["add_one", "pass", 1],
    ["count_to", "pass", 9],
  ]);
  const refuted = report.functionResults(load("unsafe").report);
  assert.deepStrictEqual(refuted.map((r) => [r.fn, r.status]), [["withdraw", "fail"]]);
  assert.match(refuted[0].message, /^refuted: ensures with result = -1/);
  assert.deepStrictEqual(results("unknown"), []);
});

test("functions: a refuted part without a refutation fails, one refuted at another function is unknown", () => {
  const text = load("split").text.replace(/^\{"kind":"failure","part":2.*$/m, "");
  const parsed = report.parseReport(text);
  assert.deepStrictEqual(report.functionResults(parsed).map((r) => [r.fn, r.status]), [["withdraw", "fail"], ["count_to", "fail"], ["main", "pass"]]);
  assert.match(report.functionResults(parsed)[1].message, /unsat, without a refutation/);
  const shared = report.parseReport(load("split").text.replace('"functions":[{"fn":"withdraw"', '"functions":[{"fn":"other","span":null},{"fn":"withdraw"'));
  assert.deepStrictEqual(report.functionResults(shared).slice(0, 2).map((r) => [r.fn, r.status]), [["other", "unknown"], ["withdraw", "fail"]]);
});

test("the status of one function's lines: its refutation, its part, its site", () => {
  const split = load("split").report;
  assert.strictEqual(report.statusWithin(split, "unsafe.rs", at("count_to", 7, 9, 17))?.status, "fail");
  assert.strictEqual(report.statusWithin(split, "unsafe.rs", at("main", 19, 19, 24))?.status, "pass");
  assert.strictEqual(report.statusWithin(load("only-main-split").report, "safe.rs", at("main", 15, 15, 20))?.status, "pass");
  // A site in a run in one query: the function's body was checked.
  assert.strictEqual(report.statusWithin(load("safe").report, "safe.rs", at("add_one", 1, 1, 3))?.status, "pass");
  assert.strictEqual(report.statusWithin(report.parseReport(""), "a.rs", at("f", 1, 1, 2)), undefined);
});

test("the status of one function's lines the report names nothing on is undecided, never passing", () => {
  // `main` run on its own in one query: a sat run, but no site of `main`.
  const main = report.statusWithin(load("only-main").report, "safe.rs", at("main", 15, 15, 20));
  assert.strictEqual(main?.status, "unknown");
  assert.match(main?.message ?? "", /split run \(thrust.split\) names every function/);
  // A refuted query elsewhere.
  assert.strictEqual(report.statusWithin(load("unsafe").report, "unsafe.rs", at("main", 19, 19, 24))?.status, "unknown");
  // `bad` is #[thrust::trusted] with a broken ensures: its body is not checked, split or not.
  for (const name of ["only-trusted", "only-trusted-split"]) {
    assert.strictEqual(report.statusWithin(load(name).report, "trusted.rs", at("bad", 1, 4, 6))?.status, "unknown", name);
  }
  // The #[cfg(test)] `twin` is not compiled; the report's `twin` is the other one.
  const twin = load("only-twin-split").report;
  assert.strictEqual(report.statusWithin(twin, "trusted.rs", at("twin", 8, 9, 12))?.status, "unknown");
  assert.strictEqual(report.statusWithin(twin, "trusted.rs", at("twin", 14, 15, 17))?.status, "pass");
});

test("a function defined inside a trusted one is no evidence for it", () => {
  // `outer` is #[thrust::trusted] with a broken `ensures`; `outer::inner`, on its lines, is checked.
  for (const name of ["only-nested", "only-nested-split"]) {
    const parsed = load(name).report;
    assert.deepStrictEqual(report.functionResults(parsed).map((r) => r.fn).slice(0, 1), ["outer::inner"], name);
    assert.strictEqual(report.statusWithin(parsed, "nested.rs", at("outer", 1, 4, 9))?.status, "unknown", name);
    assert.strictEqual(report.statusWithin(parsed, "nested.rs", at("inner", 5, 5, 7))?.status, "pass", name);
    // A function of the same name as the one defined inside it is not passed by the inner one.
    assert.strictEqual(report.statusWithin(parsed, "nested.rs", at("inner", 1, 4, 9))?.status, "unknown", name);
  }
});
