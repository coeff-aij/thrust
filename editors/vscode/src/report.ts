// Reading one Thrust run: the JSON lines of its report (THRUST_REPORT_FORMAT=json), the rustc
// diagnostics on its standard error (--error-format=json) and its exit status. Nothing here
// depends on VS Code, so the tests run under plain node.

import * as path from "path";

/// The version of the report this file reads, the `version` of its first line.
export const REPORT_VERSION = 2;

/// How the spans' columns count, as the header states it; the only convention this file reads.
export const COLUMNS: Columns = { base: 1, unit: "char", end: "exclusive" };

/// A span as the report writes it: 1-based lines and columns in characters, `end_column` after
/// the last character, the file relative to the report's root.
export interface Range {
  file: string;
  line: number;
  column: number;
  end_line: number;
  end_column: number;
}

/// A position for the editor: a file, a 1-based line and a 1-based column in characters, and the
/// end (exclusive) when the span has a width.
export interface Location {
  file: string;
  line: number;
  column: number;
  endLine?: number;
  endColumn?: number;
}

export interface FnSpan {
  fn: string;
  span: Range;
}

/// How a span's columns count: from `base`, in `unit`, `end_column` after the last (`exclusive`).
export interface Columns {
  base: number;
  unit: string;
  end: string;
}

/// The first line: the format's version, the directory relative files are in, how columns count.
export interface Header {
  version: number;
  root: string;
  columns: Columns;
}

export interface VerdictLine {
  /// `sat`, `unsat`, `timeout`, `unknown` or `error`.
  verdict: string;
  /// `one per query` or `one per part`: how many obligations a failure is refuted at.
  refutations: string;
  /// What the solver answered when it is neither `sat` nor `unsat` (`Timeout(30s)`), for a
  /// query solved in parts the first such part's (`part 1: Timeout(30s)`); null otherwise.
  message: string | null;
}

export interface Part {
  id: number;
  clauses: number;
  functions: FnSpan[];
  verdict: string;
  /// What the solver answered for the part when it is neither `sat` nor `unsat`; null otherwise.
  message: string | null;
  cached: boolean;
}

export interface Step {
  depth: number;
  fact: string;
  via: string | null;
  obligation: string | null;
  span: Range | null;
  /// The fact's unknown, and the arguments the program names with their values.
  pred: string;
  args: Value[];
}

export interface Value {
  name: string;
  value: string;
}

export interface Failure {
  part: number | null;
  constraint: string;
  fn: string | null;
  span: Range | null;
  obligation: string | null;
  premises: string[] | null;
  conclusion: string | null;
  run: Step[];
  truncated: boolean;
  values: Value[];
  inferred: string[];
  /// The written annotations the refuted obligation checks.
  annotation: Range[];
  /// The functions whose written `ensures` the run assumes at a call, at that annotation.
  assumes: FnSpan[];
}

export interface Site {
  fn: string;
  site: string;
  span: Range;
  over: string;
  template: string;
  solution: string[] | null;
  inferred: string | null;
}

export interface Constraint {
  id: string;
  fn: string;
  loop: Range | null;
  span: Range | null;
  obligation: string;
  premises: string[];
  conclusion: string;
}

export interface Report {
  header?: Header;
  verdict?: VerdictLine;
  parts: Part[];
  failures: Failure[];
  sites: Site[];
  constraints: Constraint[];
  /// Lines that are not a JSON object of a known kind.
  unparsed: string[];
}

export interface RustcSpan {
  file_name: string;
  line_start: number;
  line_end: number;
  column_start: number;
  column_end: number;
  is_primary: boolean;
  label: string | null;
}

export interface RustcDiagnostic {
  message: string;
  level: string;
  spans: RustcSpan[];
  children: RustcDiagnostic[];
}

export type Verdict = "safe" | "unsafe" | "unknown" | "error";

export interface Outcome {
  verdict: Verdict;
  /// One line saying what decided the verdict.
  detail: string;
}

export interface Related {
  location: Location;
  message: string;
}

export interface Finding {
  location: Location;
  severity: "error" | "warning" | "information";
  message: string;
  related: Related[];
  /// `thrust` locations are relative to the report's root, `rustc` ones to the run's directory.
  source: "thrust" | "rustc";
}

export interface Hint {
  location: Location;
  /// Short text for the end of the line.
  label: string;
  /// The full text, for a hover.
  tooltip: string;
  kind: "inferred" | "fact";
}

/// The location of a report's span; a zero-width span keeps its start only.
export function locationOf(range: Range | null | undefined): Location | undefined {
  if (!range) {
    return undefined;
  }
  const start = headOf(range);
  if (range.end_line === range.line && range.end_column === range.column) {
    return start;
  }
  return { ...start, endLine: range.end_line, endColumn: range.end_column };
}

/// The start of a span only: where a function or a loop is shown without covering it.
function headOf(range: Range): Location {
  return { file: range.file, line: range.line, column: range.column };
}

/// Reads the report's JSON lines.
export function parseReport(text: string): Report {
  const report: Report = { parts: [], failures: [], sites: [], constraints: [], unparsed: [] };
  for (const line of text.split("\n")) {
    if (line.trim() === "") {
      continue;
    }
    const object = parseObject(line);
    if (!addLine(report, object)) {
      report.unparsed.push(line);
    }
  }
  return report;
}

function parseObject(line: string): Record<string, unknown> | undefined {
  try {
    const value: unknown = JSON.parse(line);
    return typeof value === "object" && value !== null ? (value as Record<string, unknown>) : undefined;
  } catch {
    return undefined;
  }
}

function addLine(report: Report, object: Record<string, unknown> | undefined): boolean {
  switch (object?.kind) {
    case "report":
      report.header = object as unknown as Header;
      return true;
    case "verdict":
      report.verdict = object as unknown as VerdictLine;
      return true;
    case "part":
      report.parts.push(object as unknown as Part);
      return true;
    case "failure":
      report.failures.push(object as unknown as Failure);
      return true;
    case "site":
      report.sites.push(object as unknown as Site);
      return true;
    case "constraint":
      report.constraints.push(object as unknown as Constraint);
      return true;
    default:
      return false;
  }
}

/// Why the report cannot be read, if it cannot: it has lines but no header (a Thrust before the
/// header), a version other than the one read here, or columns counted otherwise. An empty
/// report (a run that stopped before writing one) is no refusal.
export function refusal(report: Report): string | undefined {
  if (report.header) {
    return headerRefusal(report.header);
  }
  const lines =
    report.parts.length + report.failures.length + report.sites.length + report.constraints.length + report.unparsed.length;
  return lines > 0 || report.verdict
    ? `the report has no header line (a Thrust older than report version ${REPORT_VERSION})`
    : undefined;
}

function headerRefusal(header: Header): string | undefined {
  if (header.version !== REPORT_VERSION) {
    return `the report is of version ${header.version}; this extension reads version ${REPORT_VERSION}`;
  }
  const columns = header.columns;
  if (columns?.base !== COLUMNS.base || columns.unit !== COLUMNS.unit || columns.end !== COLUMNS.end) {
    return `the report counts columns as ${JSON.stringify(columns)}; this extension reads ${JSON.stringify(COLUMNS)}`;
  }
  return undefined;
}

/// The directory the report's files are relative to: its root, against the run's directory.
export function reportRoot(report: Report, cwd: string): string {
  return path.resolve(cwd, report.header?.root ?? ".");
}

/// Reads rustc's JSON diagnostics from standard error; other lines (a panic, a wrapper's output)
/// are kept as text.
export function parseDiagnostics(stderr: string): { diagnostics: RustcDiagnostic[]; other: string[] } {
  const diagnostics: RustcDiagnostic[] = [];
  const other: string[] = [];
  for (const line of stderr.split("\n")) {
    if (line.trim() === "") {
      continue;
    }
    const object = parseObject(line);
    if (object && typeof object.message === "string" && Array.isArray(object.spans)) {
      diagnostics.push(object as unknown as RustcDiagnostic);
    } else {
      other.push(line);
    }
  }
  return { diagnostics, other };
}

const VERDICTS: Record<string, Verdict> = {
  sat: "safe",
  unsat: "unsafe",
  timeout: "unknown",
  unknown: "unknown",
  error: "error",
};

/// The verdict of a run, from the report's `verdict` line. A run without one stopped before
/// verification (a compile error, a crash) and is an error, described by rustc's first error.
export function verdictOf(exitCode: number | null, report: Report, diagnostics: RustcDiagnostic[]): Outcome {
  const refused = refusal(report);
  if (refused) {
    return { verdict: "error", detail: refused };
  }
  if (!report.verdict) {
    const firstError = diagnostics.find((d) => d.level === "error");
    return { verdict: "error", detail: firstError?.message ?? `no verdict in the report, exit status ${exitCode}` };
  }
  const verdict = VERDICTS[report.verdict.verdict] ?? "error";
  const detail = partsDetail(report.parts, report.verdict) ?? queryDetail(report.verdict, report.failures.length);
  return { verdict, detail };
}

function queryDetail(line: VerdictLine, failures: number): string {
  if (line.verdict !== "unsat") {
    return `the solver answered ${line.message ?? line.verdict}`;
  }
  return failures > 0 ? `refuted, ${line.refutations}; other obligations may fail too` : "refuted, without a refutation to show";
}

function partsDetail(parts: Part[], line: VerdictLine): string | undefined {
  if (parts.length === 0) {
    return undefined;
  }
  const count = (verdict: string) => parts.filter((p) => p.verdict === verdict).length;
  const cached = parts.filter((p) => p.cached).length;
  const failed = parts.length - count("sat") - count("unsat");
  const answered = line.message ? ` (${line.message})` : "";
  const others = failed > 0 ? `, ${failed} without an answer${answered}` : "";
  const noun = parts.length === 1 ? "part" : "parts";
  return `${parts.length} ${noun}: ${count("sat")} sat, ${count("unsat")} unsat${others}; ${cached} from the cache`;
}

const VERIFICATION_ERROR = /^verification error: /;

/// The diagnostics of a run: a refuted obligation at its span, with the annotation it checks, the
/// written contracts it assumes and the run reaching it as related information; a part that is
/// not `sat` and has no refutation at the start of each of its functions; rustc's own diagnostics
/// that have a span. rustc's `verification error` is left out when the report is read, as the
/// report places the same failure with more. `fallback` takes what has no span (a query without
/// an answer when not split, a report that cannot be read).
export function findings(report: Report, diagnostics: RustcDiagnostic[], outcome: Outcome, fallback: Location): Finding[] {
  const readable = report.verdict !== undefined && refusal(report) === undefined;
  const result = readable ? reportFindings(report, fallback) : [];
  for (const diagnostic of diagnostics) {
    if (readable && VERIFICATION_ERROR.test(diagnostic.message)) {
      continue;
    }
    const finding = rustcFinding(diagnostic);
    if (finding) {
      result.push(finding);
    }
  }
  if (result.length === 0 && outcome.verdict !== "safe") {
    result.push({
      location: fallback,
      severity: outcome.verdict === "unknown" ? "warning" : "error",
      message: `Thrust: ${outcome.verdict} (${outcome.detail})`,
      related: [],
      source: "thrust",
    });
  }
  return result;
}

function reportFindings(report: Report, fallback: Location): Finding[] {
  const parts = new Map(report.parts.map((p) => [p.id, p]));
  const result = report.failures.map((f) => failureFinding(f, f.part === null ? undefined : parts.get(f.part), report.sites, fallback));
  const refuted = new Set(report.failures.map((f) => f.part));
  for (const part of report.parts.filter((p) => p.verdict !== "sat" && !refuted.has(p.id))) {
    result.push(...partFindings(part));
  }
  return result;
}

function failureFinding(failure: Failure, part: Part | undefined, sites: Site[], fallback: Location): Finding {
  const where = failure.fn ? ` in \`${failure.fn}\`` : "";
  const lines = [`refuted: ${failure.obligation ?? "obligation"}${where}${part ? `, ${partName(part)}` : ""}`];
  if (failure.values.length > 0) {
    lines.push(`where it fails: ${formatValues(failure.values)}`);
  }
  if (failure.conclusion !== null) {
    lines.push(`${failure.constraint}: ${formatConstraint(failure.premises ?? [], failure.conclusion)}`);
  }
  if (failure.inferred.length > 0) {
    lines.push(`it goes through the contract inferred for ${failure.inferred.map((f) => `\`${f}\``).join(", ")}`);
  }
  return {
    location: locationOf(failure.span) ?? fallback,
    severity: "error",
    message: lines.join("\n"),
    related: [...annotationRelated(failure), ...assumesRelated(failure), ...runRelated(failure), ...inferredRelated(failure, sites)],
    source: "thrust",
  };
}

function partName(part: Part): string {
  return `part ${part.id} (${part.functions.map((f) => `\`${f.fn}\``).join(", ")})`;
}

function annotationRelated(failure: Failure): Related[] {
  return failure.annotation.map((range) => ({ location: locationOf(range) ?? headOf(range), message: "the annotation it checks" }));
}

function assumesRelated(failure: Failure): Related[] {
  return failure.assumes.map((a) => ({
    location: locationOf(a.span) ?? headOf(a.span),
    message: `it assumes the written contract of \`${a.fn}\``,
  }));
}

/// Each fact of the run at the start of the constraint it was derived by.
function runRelated(failure: Failure): Related[] {
  return failure.run.flatMap((step) =>
    step.span ? [{ location: headOf(step.span), message: `${step.fact}   [${step.via ?? "?"} ${step.obligation ?? ""}]` }] : [],
  );
}

function inferredRelated(failure: Failure, sites: Site[]): Related[] {
  return failure.inferred.flatMap((fn) => {
    const site = sites.find((s) => s.fn === fn && s.site === "contract");
    return site ? [{ location: headOf(site.span), message: `contract inferred for \`${fn}\`: ${site.inferred ?? site.template}` }] : [];
  });
}

/// A part that is not `sat` and has no refutation (a timeout, or a refuted part whose second run
/// gave none), at the start of each of its functions.
function partFindings(part: Part): Finding[] {
  const severity = part.verdict === "unsat" ? ("error" as const) : ("warning" as const);
  const message = `Thrust: ${part.message ?? part.verdict} in ${partName(part)}; no refutation`;
  return part.functions.map((f) => ({ location: headOf(f.span), severity, message, related: [], source: "thrust" as const }));
}

function rustcFinding(diagnostic: RustcDiagnostic): Finding | undefined {
  const primary = diagnostic.spans.find((s) => s.is_primary);
  if (!primary || (diagnostic.level !== "error" && diagnostic.level !== "warning")) {
    return undefined;
  }
  const notes = diagnostic.children.filter((c) => c.spans.length === 0).map((c) => `${c.level}: ${c.message}`);
  const related = diagnostic.spans
    .filter((s) => s !== primary && s.label)
    .map((s) => ({ location: rustcLocation(s), message: s.label ?? "" }))
    .concat(
      diagnostic.children.flatMap((c) =>
        c.spans.map((s) => ({ location: rustcLocation(s), message: `${c.level}: ${c.message}` })),
      ),
    );
  return {
    location: rustcLocation(primary),
    severity: diagnostic.level === "error" ? "error" : "warning",
    message: [diagnostic.message, ...(primary.label ? [primary.label] : []), ...notes].join("\n"),
    related,
    source: "rustc",
  };
}

function rustcLocation(span: RustcSpan): Location {
  return {
    file: span.file_name,
    line: span.line_start,
    column: span.column_start,
    endLine: span.line_end,
    endColumn: span.column_end,
  };
}

const LABEL_LIMIT = 100;

/// The inlay hints of a run: the inferred contract of each function and invariant of each loop at
/// its span, and, for each refuted obligation, its values and the facts of the run at the code
/// that derived them.
export function hints(report: Report): Hint[] {
  if (refusal(report)) {
    return [];
  }
  const result = report.sites.flatMap(siteHint);
  for (const failure of report.failures) {
    result.push(...failureHints(failure));
  }
  return result;
}

function siteHint(site: Site): Hint[] {
  if (site.inferred === null || (site.site !== "contract" && site.site !== "loop")) {
    return [];
  }
  const what = site.site === "contract" ? "inferred contract" : "inferred invariant";
  const tooltip = [`${what} of \`${site.fn}\`:`, "", site.inferred, "", "template:", site.template]
    .concat(site.solution ? ["", "solution:", ...site.solution] : [])
    .join("\n");
  return [{ location: headOf(site.span), label: truncate(`${what}: ${site.inferred}`), tooltip, kind: "inferred" }];
}

/// One hint per line: the values where the obligation fails, and the facts derived by the
/// constraints of that line, each unknown's arguments by variable with their values latest first
/// (`i = 2 ← 1 ← 0`).
function failureHints(failure: Failure): Hint[] {
  const byLine = new Map<string, { location: Location; fails?: string; steps: Step[] }>();
  const entry = (location: Location) => {
    const key = `${location.file}:${location.line}`;
    const found = byLine.get(key) ?? { location, steps: [] };
    byLine.set(key, found);
    return found;
  };
  if (failure.span && failure.values.length > 0) {
    entry(headOf(failure.span)).fails = `fails with ${formatValues(failure.values)}`;
  }
  for (const step of failure.run) {
    if (step.span) {
      entry(headOf(step.span)).steps.push(step);
    }
  }
  return [...byLine.values()].map(({ location, fails, steps }) => {
    const segments = (fails ? [fails] : []).concat(byPred(steps).map(stepsLabel));
    const facts = (fails ? [fails] : []).concat(steps.map((s) => s.fact));
    return {
      location,
      label: truncate(segments.join("; ")),
      tooltip: [`counterexample of ${failure.constraint} (${failure.obligation ?? "obligation"}):`, "", ...facts].join("\n"),
      kind: "fact" as const,
    };
  });
}

/// The steps grouped by their unknown, in the order the unknowns first occur.
function byPred(steps: Step[]): Step[][] {
  const groups = new Map<string, Step[]>();
  for (const step of steps) {
    groups.set(step.pred, [...(groups.get(step.pred) ?? []), step]);
  }
  return [...groups.values()];
}

/// The steps of one unknown, each variable once with its values in the steps' order, a value
/// repeated in the next step said once; the fact itself when the program names no argument.
function stepsLabel(steps: Step[]): string {
  const values = new Map<string, string[]>();
  for (const step of steps) {
    for (const arg of step.args) {
      const seen = values.get(arg.name) ?? [];
      if (seen[seen.length - 1] !== arg.value) {
        seen.push(arg.value);
      }
      values.set(arg.name, seen);
    }
  }
  if (values.size === 0) {
    return steps.map((s) => s.fact).join("  ←  ");
  }
  return [...values].map(([name, seen]) => `${name} = ${seen.join(" ← ")}`).join(", ");
}

export function formatValues(values: Value[]): string {
  return values.map((v) => `${v.name} = ${v.value}`).join(", ");
}

export function formatConstraint(premises: string[], conclusion: string): string {
  return premises.length === 0 ? conclusion : `(${premises.join(" ∧ ")}) ==> ${conclusion}`;
}

function truncate(text: string): string {
  return text.length <= LABEL_LIMIT ? text : `${text.slice(0, LABEL_LIMIT - 1)}…`;
}

/// The location with its file resolved against `base`.
export function resolveLocation(location: Location, base: string): Location {
  return { ...location, file: path.resolve(base, location.file) };
}

/// The finding and its related information with their files resolved: Thrust's against the
/// report's root, rustc's against the run's directory.
export function resolveFinding(finding: Finding, root: string, cwd: string): Finding {
  const base = finding.source === "thrust" ? root : cwd;
  return {
    ...finding,
    location: resolveLocation(finding.location, base),
    related: finding.related.map((r) => ({ ...r, location: resolveLocation(r.location, base) })),
  };
}

/// The 1-based UTF-16 column, as VS Code counts, of the 1-based column in characters, as Thrust
/// and rustc count, on the line `text`.
export function utf16Column(text: string, column: number): number {
  return Array.from(text).slice(0, Math.max(column - 1, 0)).join("").length + 1;
}

/// What a run says of one function: `pass` when its obligations hold, `fail` when one is refuted,
/// `unknown` when the run decides neither (no answer, or a refutation elsewhere in its query).
export type Status = "pass" | "fail" | "unknown";

export interface FunctionResult {
  /// The function as the report names it (`Pair::twice`, `<Pair as Scale>::scale`).
  fn: string;
  /// Where it is: its part's span (the whole function), else its contract site's or its first
  /// failure's.
  span: Range | null;
  status: Status;
  /// Why, in one line.
  message: string;
  /// The refutations at it.
  failures: Failure[];
}

/// The status of each function the report names, in the order it first names them. A run split
/// in parts (`THRUST_SPLIT`) names every function, each with its part's verdict; a run in one
/// query names only those with an inferred contract, a loop or a refutation.
export function functionResults(report: Report): FunctionResult[] {
  if (refusal(report) || !report.verdict) {
    return [];
  }
  return report.parts.length > 0 ? partResults(report) : queryResults(report, report.verdict);
}

function failuresAt(report: Report, fn: string): Failure[] {
  return report.failures.filter((f) => f.fn === fn);
}

function partResults(report: Report): FunctionResult[] {
  return report.parts.flatMap((part) =>
    part.functions.map((f) => {
      const failures = failuresAt(report, f.fn).filter((x) => x.part === part.id);
      const refuted = report.failures.some((x) => x.part === part.id);
      return { fn: f.fn, span: f.span, failures, ...partStatus(part, failures, refuted) };
    }),
  );
}

function partStatus(part: Part, failures: Failure[], refuted: boolean): { status: Status; message: string } {
  const name = partName(part);
  if (part.verdict === "sat") {
    return { status: "pass", message: `${name}: sat${part.cached ? " (from the cache)" : ""}` };
  }
  if (part.verdict !== "unsat") {
    return { status: "unknown", message: `${name}: ${part.message ?? part.verdict}` };
  }
  if (failures.length > 0) {
    return { status: "fail", message: failures.map(failureLine).join("\n") };
  }
  return refuted
    ? { status: "unknown", message: `${name}: refuted at another function of the part` }
    : { status: "fail", message: `${name}: unsat, without a refutation` };
}

function queryResults(report: Report, line: VerdictLine): FunctionResult[] {
  const names: string[] = [];
  for (const fn of [...report.sites.map((s) => s.fn), ...report.failures.flatMap((f) => (f.fn ? [f.fn] : []))]) {
    if (!names.includes(fn)) {
      names.push(fn);
    }
  }
  return names.map((fn) => {
    const failures = failuresAt(report, fn);
    const site = report.sites.find((s) => s.fn === fn && s.site === "contract");
    const span = site?.span ?? failures[0]?.span ?? report.sites.find((s) => s.fn === fn)?.span ?? null;
    return { fn, span, failures, ...queryStatus(line, failures) };
  });
}

function queryStatus(line: VerdictLine, failures: Failure[]): { status: Status; message: string } {
  if (failures.length > 0) {
    return { status: "fail", message: failures.map(failureLine).join("\n") };
  }
  if (line.verdict === "sat") {
    return { status: "pass", message: "the query is sat" };
  }
  if (line.verdict === "unsat") {
    return {
      status: "unknown",
      message: `the query is refuted elsewhere, ${line.refutations}; split it (THRUST_SPLIT) to decide each function`,
    };
  }
  return { status: "unknown", message: `the solver answered ${line.message ?? line.verdict}` };
}

function failureLine(failure: Failure): string {
  const values = failure.values.length > 0 ? ` with ${formatValues(failure.values)}` : "";
  return `refuted: ${failure.obligation ?? "obligation"}${values}`;
}

/// The status of the function on the lines `line` to `endLine` of `file` (relative to the
/// report's root), in a run of that function only (`THRUST_VERIFY_ONLY`): failing when a
/// refutation is in it, else its part's when the run is split, else the run's when it is sat;
/// unknown otherwise, as other functions the run checks may be what fails.
export function statusWithin(report: Report, file: string, line: number, endLine: number): FunctionResult | undefined {
  if (refusal(report) || !report.verdict) {
    return undefined;
  }
  const inside = (span: Range | null) => span !== null && span.file === file && span.line >= line && span.line <= endLine;
  const results = functionResults(report);
  const own = results.filter((r) => inside(r.span) || r.failures.some((f) => inside(f.span)));
  const failed = own.find((r) => r.status === "fail");
  if (failed || own.length > 0) {
    return failed ?? own[0];
  }
  const fn = `lines ${line}-${endLine}`;
  return { fn, span: null, failures: [], ...queryStatus(report.verdict, []) };
}
