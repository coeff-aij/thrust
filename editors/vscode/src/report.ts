// Reading one Thrust run: the JSON lines of its report (THRUST_REPORT_FORMAT=json), the rustc
// diagnostics on its standard error (--error-format=json) and its exit status. Nothing here
// depends on VS Code, so the tests run under plain node.

import * as path from "path";

/// A position as Thrust and rustc print it: a file, a 1-based line and a 1-based column.
export interface Location {
  file: string;
  line: number;
  column: number;
  /// The end, when rustc gives one; Thrust's report gives only the start.
  endLine?: number;
  endColumn?: number;
}

export interface Part {
  functions: string[];
  verdict: string;
  cached: boolean;
}

export interface Step {
  depth: number;
  fact: string;
  via: string | null;
}

export interface Value {
  name: string;
  value: string;
}

export interface Failure {
  constraint: string;
  fn: string | null;
  span: string | null;
  obligation: string | null;
  premises: string[] | null;
  conclusion: string | null;
  run: Step[];
  truncated: boolean;
  values: Value[];
  inferred: string[];
}

export interface Site {
  fn: string;
  site: string;
  span: string;
  over: string;
  template: string;
  solution: string[] | null;
  inferred: string | null;
}

export interface Constraint {
  id: string;
  fn: string;
  loop: string | null;
  span: string | null;
  obligation: string;
  premises: string[];
  conclusion: string;
}

export interface Report {
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

/// Parses `file:line:column`, the form of every span in the report. The file may itself contain
/// colons, so the line and the column are the last two fields.
export function parseLocation(span: string | null | undefined): Location | undefined {
  if (!span) {
    return undefined;
  }
  const match = /^(.*):(\d+):(\d+)$/.exec(span);
  if (!match) {
    return undefined;
  }
  return { file: match[1], line: Number(match[2]), column: Number(match[3]) };
}

/// Reads the report's JSON lines into its four kinds of line.
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

const VERIFICATION_ERROR = /^verification error: (.*)$/;

/// The solver's answers the run reports as errors: `Unsat`, `Timeout(2s)`, ...
function verificationErrors(diagnostics: RustcDiagnostic[]): string[] {
  return diagnostics
    .map((d) => VERIFICATION_ERROR.exec(d.message)?.[1])
    .filter((kind): kind is string => kind !== undefined);
}

/// The verdict of a run. Exit 0 is safe; otherwise a refuted part or query is unsafe, a part or
/// query without an answer (a timeout, `unknown`, a solver error) is unknown, and a failure before
/// any solver answer (a compile error, a crash) is an error.
export function verdictOf(exitCode: number | null, report: Report, diagnostics: RustcDiagnostic[]): Outcome {
  if (exitCode === 0) {
    return { verdict: "safe", detail: partsDetail(report.parts) ?? "verified" };
  }
  const answers = verificationErrors(diagnostics).concat(
    report.parts.filter((p) => p.verdict !== "sat").map((p) => p.verdict),
  );
  const refuted = answers.filter((a) => a.toLowerCase().startsWith("unsat"));
  if (refuted.length > 0) {
    return { verdict: "unsafe", detail: partsDetail(report.parts) ?? "refuted" };
  }
  if (answers.length > 0) {
    return { verdict: "unknown", detail: partsDetail(report.parts) ?? answers[0] };
  }
  const firstError = diagnostics.find((d) => d.level === "error");
  return { verdict: "error", detail: firstError?.message ?? `exit status ${exitCode}` };
}

function partsDetail(parts: Part[]): string | undefined {
  if (parts.length === 0) {
    return undefined;
  }
  const count = (verdict: string) => parts.filter((p) => p.verdict === verdict).length;
  const cached = parts.filter((p) => p.cached).length;
  const failed = parts.length - count("sat") - count("unsat");
  const others = failed > 0 ? `, ${failed} without an answer` : "";
  return `${parts.length} parts: ${count("sat")} sat, ${count("unsat")} unsat${others}; ${cached} from the cache`;
}

/// The diagnostics of a run: a refuted obligation at its span, with the run reaching it as
/// related information; a part without an answer at the entries of its functions; rustc's own
/// diagnostics that have a span. `fallback` takes what has no span (a query without an answer
/// when not split).
export function findings(report: Report, diagnostics: RustcDiagnostic[], outcome: Outcome, fallback: Location): Finding[] {
  const constraints = new Map(report.constraints.map((c) => [c.id, c]));
  const result: Finding[] = [];
  for (const failure of report.failures) {
    const finding = failureFinding(failure, constraints, report.sites);
    if (finding) {
      result.push(finding);
    }
  }
  for (const part of report.parts.filter((p) => p.verdict !== "sat" && p.verdict !== "unsat")) {
    result.push(...partFindings(part, report));
  }
  for (const diagnostic of diagnostics) {
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

function failureFinding(failure: Failure, constraints: Map<string, Constraint>, sites: Site[]): Finding | undefined {
  const location = parseLocation(failure.span);
  if (!location) {
    return undefined;
  }
  const lines = [`refuted: ${failure.obligation ?? "obligation"}${failure.fn ? ` in \`${failure.fn}\`` : ""}`];
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
    location,
    severity: "error",
    message: lines.join("\n"),
    related: runRelated(failure, constraints).concat(inferredRelated(failure, sites)),
    source: "thrust",
  };
}

/// Each fact of the run at the code of the constraint it was derived by.
function runRelated(failure: Failure, constraints: Map<string, Constraint>): Related[] {
  const related: Related[] = [];
  for (const step of failure.run) {
    const constraint = step.via ? constraints.get(step.via) : undefined;
    const location = parseLocation(constraint?.span);
    if (!constraint || !location) {
      continue;
    }
    related.push({ location, message: `${step.fact}   [${constraint.id} ${constraint.obligation}]` });
  }
  return related;
}

function inferredRelated(failure: Failure, sites: Site[]): Related[] {
  return failure.inferred.flatMap((fn) => {
    const site = sites.find((s) => s.fn === fn && s.site === "contract");
    const location = parseLocation(site?.span);
    return location ? [{ location, message: `contract inferred for \`${fn}\`: ${site?.inferred ?? site?.template}` }] : [];
  });
}

/// A part without an answer names only its functions; it is shown at each function's entry, the
/// span of its contract's template or of its `function entry` constraint.
function partFindings(part: Part, report: Report): Finding[] {
  const message = `Thrust: ${part.verdict} in the part of ${part.functions.map((f) => `\`${f}\``).join(", ")}; no refutation`;
  return part.functions.flatMap((fn) => {
    const location = functionLocation(fn, report);
    return location ? [{ location, severity: "warning" as const, message, related: [], source: "thrust" as const }] : [];
  });
}

function functionLocation(fn: string, report: Report): Location | undefined {
  const contract = report.sites.find((s) => s.fn === fn && s.site === "contract");
  const entry = report.constraints.find((c) => c.fn === fn && c.obligation === "function entry");
  return parseLocation(contract?.span) ?? parseLocation(entry?.span);
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
  const result = report.sites.flatMap(siteHint);
  const constraints = new Map(report.constraints.map((c) => [c.id, c]));
  for (const failure of report.failures) {
    result.push(...failureHints(failure, constraints));
  }
  return result;
}

function siteHint(site: Site): Hint[] {
  const location = parseLocation(site.span);
  if (!location || site.inferred === null || (site.site !== "contract" && site.site !== "loop")) {
    return [];
  }
  const what = site.site === "contract" ? "inferred contract" : "inferred invariant";
  const tooltip = [`${what} of \`${site.fn}\`:`, "", site.inferred, "", "template:", site.template]
    .concat(site.solution ? ["", "solution:", ...site.solution] : [])
    .join("\n");
  return [{ location, label: truncate(`${what}: ${site.inferred}`), tooltip, kind: "inferred" }];
}

/// One hint per line: the facts derived by the constraints of one line are joined, latest first.
function failureHints(failure: Failure, constraints: Map<string, Constraint>): Hint[] {
  const byLine = new Map<string, { location: Location; facts: string[] }>();
  const add = (location: Location, fact: string) => {
    const key = `${location.file}:${location.line}`;
    const entry = byLine.get(key) ?? { location, facts: [] };
    entry.facts.push(fact);
    byLine.set(key, entry);
  };
  const failing = parseLocation(failure.span);
  if (failing && failure.values.length > 0) {
    add(failing, `fails with ${formatValues(failure.values)}`);
  }
  for (const step of failure.run) {
    const location = parseLocation(step.via ? constraints.get(step.via)?.span : undefined);
    if (location) {
      add(location, step.fact);
    }
  }
  return [...byLine.values()].map(({ location, facts }) => ({
    location,
    label: truncate(facts.join("  ←  ")),
    tooltip: [`counterexample of ${failure.constraint} (${failure.obligation ?? "obligation"}):`, "", ...facts].join("\n"),
    kind: "fact" as const,
  }));
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

/// The location with its file resolved against the directory the run was started in.
export function resolveLocation(location: Location, cwd: string): Location {
  return { ...location, file: path.resolve(cwd, location.file) };
}
