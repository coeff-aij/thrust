// The VS Code side: runs Thrust on a Rust file, or with `cargo check` on the cargo workspace the
// file belongs to (on command, on save, for one function from a code lens or from the Testing
// view), and shows the run's findings as diagnostics, its inferred contracts and counterexample
// facts as inlay hints and hovers, the status of each function in the Testing view and the
// verdict in the status bar.

import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";
import * as cargo from "./cargo";
import * as items from "./items";
import * as report from "./report";
import { run, RunConfig } from "./runner";

export function activate(context: vscode.ExtensionContext): void {
  const wrapper = context.asAbsolutePath(path.join("bin", "thrust-rustc-cargo"));
  // cargo runs it as RUSTC; an installed package need not keep its mode.
  fs.chmodSync(wrapper, 0o755);
  const thrust = new Thrust(wrapper);
  context.subscriptions.push(
    thrust,
    vscode.commands.registerCommand("thrust.verifyFile", () => {
      const document = vscode.window.activeTextEditor?.document;
      if (document?.languageId !== "rust") {
        vscode.window.showWarningMessage("Thrust: the active editor holds no Rust file.");
        return;
      }
      void thrust.verify(document);
    }),
    vscode.commands.registerCommand("thrust.verifyFunction", async (uri: string, fn: items.FnItem) => {
      void thrust.verify(await vscode.workspace.openTextDocument(vscode.Uri.parse(uri)), fn);
    }),
    vscode.commands.registerCommand("thrust.showOutput", () => thrust.output.show()),
    vscode.workspace.onDidSaveTextDocument((document) => {
      if (document.languageId === "rust" && settings(document).get<boolean>("verifyOnSave", true)) {
        void thrust.verify(document);
      }
    }),
    vscode.languages.registerInlayHintsProvider({ language: "rust" }, thrust),
    vscode.languages.registerHoverProvider({ language: "rust" }, thrust),
    vscode.languages.registerCodeLensProvider({ language: "rust" }, thrust),
  );
}

export function deactivate(): void {}

function settings(document: vscode.TextDocument): vscode.WorkspaceConfiguration {
  return vscode.workspace.getConfiguration("thrust", document.uri);
}

function folderOf(document: vscode.TextDocument): string {
  return vscode.workspace.getWorkspaceFolder(document.uri)?.uri.fsPath ?? path.dirname(document.uri.fsPath);
}

function runConfig(document: vscode.TextDocument): cargo.CargoConfig {
  const config = settings(document);
  const cacheDir = config.get<string>("cacheDir", "");
  return {
    command: config.get<string[]>("command", ["thrust-rustc"]),
    extraArgs: config.get<string[]>("extraArgs", []),
    env: config.get<Record<string, string>>("env", {}),
    split: config.get<number>("split", 0),
    cacheDir: cacheDir === "" ? "" : path.resolve(folderOf(document), cacheDir),
    timeoutSecs: config.get<number>("timeoutSecs", 300),
    cargo: config.get<string[]>("cargoCommand", ["cargo"]),
  };
}

/// What one crate, or the one file, of a run left, ready to show.
interface Unit {
  /// The Testing view's item of the crate or the file.
  id: string;
  label: string;
  /// The file the unit's item and findings without a place are at.
  file: string;
  report: report.Report;
  diagnostics: report.RustcDiagnostic[];
  outcome: report.Outcome;
  /// The directories the report's files and rustc's are relative to.
  root: string;
  cwd: string;
}

/// A run of one function only: its lines, and the path `THRUST_VERIFY_ONLY` names it by.
interface Scope {
  file: string;
  fn: items.FnItem;
  selection: string;
}

/// Where a document is verified: as a file of its own, or as a file of a cargo target.
type Place = { kind: "file"; file: string } | { kind: "cargo"; metadata: cargo.Metadata; target: cargo.Target };

class Thrust implements vscode.InlayHintsProvider, vscode.HoverProvider, vscode.CodeLensProvider, vscode.Disposable {
  readonly output = vscode.window.createOutputChannel("Thrust");
  private readonly diagnostics = vscode.languages.createDiagnosticCollection("thrust");
  private readonly status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 10);
  private readonly hintsChanged = new vscode.EventEmitter<void>();
  readonly onDidChangeInlayHints = this.hintsChanged.event;
  private readonly tests = vscode.tests.createTestController("thrust", "Thrust");
  /// By file path: the hints of the last run, for the inlay hints and the hovers.
  private readonly shown = new Map<string, report.Hint[]>();
  /// The run in progress, by file or by cargo workspace.
  private readonly running = new Map<string, AbortController>();
  /// The Testing view's items of functions, as opposed to those of crates and files.
  private readonly fnItems = new WeakSet<vscode.TestItem>();

  constructor(private readonly wrapper: string) {
    this.status.command = "thrust.showOutput";
    this.status.text = "$(shield) Thrust";
    this.status.tooltip = "Thrust: not run yet";
    this.status.show();
    this.tests.createRunProfile("Verify", vscode.TestRunProfileKind.Run, (request, token) => this.runTests(request, token), true);
  }

  dispose(): void {
    for (const controller of this.running.values()) {
      controller.abort();
    }
    this.output.dispose();
    this.diagnostics.dispose();
    this.status.dispose();
    this.hintsChanged.dispose();
    this.tests.dispose();
  }

  /// Verifies the document, or only the function `fn` of it, and shows the result; `testRun`
  /// takes the functions' statuses when the Testing view started the run.
  async verify(document: vscode.TextDocument, fn?: items.FnItem, testRun?: vscode.TestRun): Promise<void> {
    const config = runConfig(document);
    let place: Place;
    try {
      place = await placeOf(document, config);
    } catch (err) {
      this.showStatus("error", String(err), path.basename(document.uri.fsPath));
      return;
    }
    const key = place.kind === "cargo" ? place.metadata.workspaceRoot : place.file;
    this.running.get(key)?.abort();
    const controller = new AbortController();
    this.running.set(key, controller);
    const scope = fn ? scopeOf(document, place, fn) : undefined;
    this.status.text = `$(sync~spin) Thrust: verifying${scope ? ` ${scope.selection}` : ""}`;
    this.status.tooltip = path.basename(document.uri.fsPath);
    let units: Unit[] | undefined;
    try {
      units =
        place.kind === "cargo"
          ? await this.runCargo(place, config, scope, controller.signal)
          : await this.runFile(place.file, config, scope, controller.signal);
    } catch (err) {
      this.showStatus("error", String(err), path.basename(document.uri.fsPath));
      return;
    } finally {
      if (this.running.get(key) === controller) {
        this.running.delete(key);
      }
    }
    if (units) {
      this.show(units, scope, testRun);
    }
  }

  private async runFile(file: string, config: RunConfig, scope: Scope | undefined, signal: AbortSignal): Promise<Unit[] | undefined> {
    const result = await run(file, config, signal, scope?.selection);
    if (result.cancelled) {
      return undefined;
    }
    const inv = result.invocation;
    this.log(inv, result);
    const parsed = report.parseReport(result.report);
    const { diagnostics } = report.parseDiagnostics(result.stderr);
    const outcome = result.timedOut ? stopped() : report.verdictOf(result.exitCode, parsed, diagnostics);
    const root = report.reportRoot(parsed, inv.cwd);
    return [{ id: file, label: path.basename(file), file, report: parsed, diagnostics, outcome, root, cwd: inv.cwd }];
  }

  private async runCargo(
    place: { metadata: cargo.Metadata; target: cargo.Target },
    config: cargo.CargoConfig,
    scope: Scope | undefined,
    signal: AbortSignal,
  ): Promise<Unit[] | undefined> {
    const only = scope ? { target: place.target, selection: scope.selection } : undefined;
    const result = await cargo.runCargo(place.metadata, config, this.wrapper, only, signal);
    if (result.cancelled) {
      return undefined;
    }
    this.log(result.invocation, result);
    const cwd = place.metadata.workspaceRoot;
    return result.crates.map((crate) => {
      const parsed = report.parseReport(crate.report);
      const t = crate.target;
      return {
        id: `${t.package}/${t.kind}/${t.name}`,
        label: `${t.package} (${t.kind === "bin" ? `bin ${t.name}` : t.kind})`,
        file: t.srcPath,
        report: parsed,
        diagnostics: crate.diagnostics,
        outcome: result.timedOut ? stopped() : report.verdictOf(null, parsed, crate.diagnostics),
        root: report.reportRoot(parsed, cwd),
        cwd,
      };
    });
  }

  private log(
    command: { cwd: string; env: Record<string, string>; program: string; args: string[] },
    result: { exitCode: number | null; timedOut: boolean; durationMs: number; stderr: string },
  ): void {
    const vars = Object.entries(command.env)
      .map(([k, v]) => `${k}=${JSON.stringify(v)}`)
      .join(" ");
    this.output.appendLine(`$ cd ${command.cwd} && ${vars} ${command.program} ${command.args.join(" ")}`);
    this.output.appendLine(`exit ${result.exitCode}${result.timedOut ? " (stopped at the time limit)" : ""}, ${result.durationMs} ms`);
    if (result.stderr.trim() !== "") {
      this.output.appendLine(result.stderr.trimEnd());
    }
  }

  private show(units: Unit[], scope: Scope | undefined, testRun: vscode.TestRun | undefined): void {
    const findings = units.flatMap(unitFindings);
    const hints = units.flatMap((u) => report.hints(u.report).map((h) => ({ ...h, location: report.resolveLocation(h.location, u.root) })));
    this.publish(findings, hints, scope);
    this.showTests(units, scope, testRun);
    const verdict = overallVerdict(units.map((u) => u.outcome.verdict));
    const detail =
      units.length === 1 ? units[0].outcome.detail : units.map((u) => `${u.label}: ${u.outcome.verdict} (${u.outcome.detail})`).join("\n");
    this.showStatus(verdict, detail || "no crate was checked", scope ? scope.selection : units.map((u) => u.label).join(", "));
  }

  /// Replaces the diagnostics and hints with the run's; for a run of one function, only those on
  /// its lines.
  private publish(findings: report.Finding[], hints: report.Hint[], scope: Scope | undefined): void {
    const inScope = (location: report.Location) =>
      !scope || (location.file === scope.file && location.line >= scope.fn.line && location.line <= scope.fn.endLine);
    const byFile = new Map<string, report.Finding[]>();
    for (const finding of findings.filter((f) => inScope(f.location))) {
      byFile.set(finding.location.file, [...(byFile.get(finding.location.file) ?? []), finding]);
    }
    if (!scope) {
      this.diagnostics.clear();
      this.shown.clear();
    }
    const kept = (uri: vscode.Uri) =>
      (this.diagnostics.get(uri) ?? []).filter((d) => !inScope({ file: uri.fsPath, line: d.range.start.line + 1, column: 1 }));
    const files = scope ? new Set([...byFile.keys(), scope.file]) : new Set(byFile.keys());
    const lines = new Lines();
    for (const file of files) {
      const uri = vscode.Uri.file(file);
      const fresh = (byFile.get(file) ?? []).map((f) => toDiagnostic(f, lines));
      this.diagnostics.set(uri, scope ? [...kept(uri), ...fresh] : fresh);
    }
    if (scope) {
      this.shown.set(scope.file, (this.shown.get(scope.file) ?? []).filter((h) => !inScope(h.location)));
    }
    for (const hint of hints.filter((h) => inScope(h.location))) {
      this.shown.set(hint.location.file, [...(this.shown.get(hint.location.file) ?? []), hint]);
    }
    this.hintsChanged.fire();
  }

  private showStatus(verdict: report.Verdict, detail: string, what: string): void {
    const icon = { safe: "$(pass)", unsafe: "$(error)", unknown: "$(question)", error: "$(warning)" }[verdict];
    this.status.text = `${icon} Thrust: ${verdict}`;
    this.status.tooltip = `${what}: ${detail}\nClick for the output of the run.`;
  }

  /// The Testing view: an item per crate or file with its verdict, and under it an item per
  /// function the report names with its status. A run of one function updates that function's
  /// item only.
  private showTests(units: Unit[], scope: Scope | undefined, testRun: vscode.TestRun | undefined): void {
    const target = testRun ?? this.tests.createTestRun(new vscode.TestRunRequest(), "Thrust", false);
    for (const unit of units) {
      const unitItem = this.unitItem(unit);
      if (scope) {
        this.showScoped(unit, unitItem, scope, target);
        continue;
      }
      const results = report.functionResults(unit.report);
      unitItem.children.replace(results.map((r) => this.fnItem(unit, r)));
      for (const result of results) {
        const item = unitItem.children.get(fnItemId(unit, result.fn));
        if (item) {
          setState(target, item, result.status, resultMessages(result, unit));
        }
      }
      setState(target, unitItem, unitStatus(unit.outcome.verdict), [new vscode.TestMessage(unit.outcome.detail)]);
    }
    if (!testRun) {
      target.end();
    }
  }

  private showScoped(unit: Unit, unitItem: vscode.TestItem, scope: Scope, testRun: vscode.TestRun): void {
    const file = path.relative(unit.root, scope.file);
    const result = report.statusWithin(unit.report, file, scope.fn.line, scope.fn.endLine);
    if (!result) {
      return;
    }
    const named = result.span ? result : { ...result, fn: scope.selection, span: spanOf(file, scope.fn) };
    const item = unitItem.children.get(fnItemId(unit, named.fn)) ?? this.fnItem(unit, named);
    unitItem.children.add(item);
    setState(testRun, item, named.status, resultMessages(named, unit));
  }

  private unitItem(unit: Unit): vscode.TestItem {
    const existing = this.tests.items.get(unit.id);
    if (existing) {
      return existing;
    }
    const item = this.tests.createTestItem(unit.id, unit.label, vscode.Uri.file(unit.file));
    this.tests.items.add(item);
    return item;
  }

  private fnItem(unit: Unit, result: report.FunctionResult): vscode.TestItem {
    const file = result.span ? path.resolve(unit.root, result.span.file) : unit.file;
    const item = this.tests.createTestItem(fnItemId(unit, result.fn), result.fn, vscode.Uri.file(file));
    if (result.span) {
      item.range = new vscode.Range(result.span.line - 1, 0, result.span.end_line - 1, 0);
    }
    this.fnItems.add(item);
    return item;
  }

  /// A run from the Testing view: a function's item runs that function, a crate's or a file's
  /// item (or all of them) the whole of it.
  private async runTests(request: vscode.TestRunRequest, token: vscode.CancellationToken): Promise<void> {
    const testRun = this.tests.createTestRun(request, "Thrust", false);
    const requested: vscode.TestItem[] = [];
    if (request.include) {
      requested.push(...request.include);
    } else {
      this.tests.items.forEach((item) => requested.push(item));
    }
    for (const item of requested) {
      if (token.isCancellationRequested) {
        break;
      }
      testRun.started(item);
      await this.runItem(item, testRun);
    }
    testRun.end();
  }

  /// Runs an item: a function's by the function of the file at its line, as the code lens does.
  private async runItem(item: vscode.TestItem, testRun: vscode.TestRun): Promise<void> {
    if (!item.uri) {
      return;
    }
    const document = await vscode.workspace.openTextDocument(item.uri);
    const line = (item.range?.start.line ?? 0) + 1;
    const fn = this.fnItems.has(item)
      ? items.functionsIn(document.getText()).find((f) => f.line <= line && line <= f.endLine)
      : undefined;
    await this.verify(document, fn, testRun);
  }

  provideCodeLenses(document: vscode.TextDocument): vscode.CodeLens[] {
    if (!settings(document).get<boolean>("codeLens", true)) {
      return [];
    }
    return items.functionsIn(document.getText()).map(
      (fn) =>
        new vscode.CodeLens(new vscode.Range(fn.line - 1, 0, fn.line - 1, 0), {
          title: "Verify this function",
          tooltip: `Thrust with THRUST_VERIFY_ONLY on ${fn.path.join("::")}`,
          command: "thrust.verifyFunction",
          arguments: [document.uri.toString(), fn],
        }),
    );
  }

  provideInlayHints(document: vscode.TextDocument, range: vscode.Range): vscode.InlayHint[] {
    if (!settings(document).get<boolean>("inlayHints", true)) {
      return [];
    }
    const hints = this.shown.get(document.uri.fsPath) ?? [];
    return hints
      .filter((h) => h.location.line - 1 >= range.start.line && h.location.line - 1 <= range.end.line)
      .filter((h) => h.location.line - 1 < document.lineCount)
      .map((h) => {
        const end = document.lineAt(h.location.line - 1).range.end;
        const hint = new vscode.InlayHint(end, h.label);
        hint.paddingLeft = true;
        hint.tooltip = new vscode.MarkdownString().appendCodeblock(h.tooltip, "text");
        return hint;
      });
  }

  provideHover(document: vscode.TextDocument, position: vscode.Position): vscode.Hover | undefined {
    const hints = this.shown.get(document.uri.fsPath) ?? [];
    const onLine = hints.filter((h) => h.location.line - 1 === position.line);
    if (onLine.length === 0) {
      return undefined;
    }
    const markdown = new vscode.MarkdownString();
    for (const hint of onLine) {
      markdown.appendCodeblock(hint.tooltip, "text");
    }
    return new vscode.Hover(markdown);
  }
}

/// A file of a cargo target when the workspace folder has a Cargo.toml and a target of the
/// workspace holds the file; otherwise the file on its own.
async function placeOf(document: vscode.TextDocument, config: cargo.CargoConfig): Promise<Place> {
  const file = document.uri.fsPath;
  const folder = folderOf(document);
  if (!fs.existsSync(path.join(folder, "Cargo.toml"))) {
    return { kind: "file", file };
  }
  const metadata = await cargo.metadataOf(folder, config.cargo);
  const target = cargo.targetOf(file, metadata);
  return target ? { kind: "cargo", metadata, target } : { kind: "file", file };
}

/// The function `fn` of the document, named for `THRUST_VERIFY_ONLY` by its module in the crate:
/// the file's place under the cargo target's root, or the crate root for a file on its own.
function scopeOf(document: vscode.TextDocument, place: Place, fn: items.FnItem): Scope {
  const file = document.uri.fsPath;
  const modulePath = place.kind === "cargo" ? (items.modulePathOf(file, place.target.srcPath) ?? []) : [];
  return { file, fn, selection: items.selectionPath(modulePath, fn) };
}

function stopped(): report.Outcome {
  return { verdict: "unknown", detail: "stopped at thrust.timeoutSecs" };
}

function spanOf(file: string, fn: items.FnItem): report.Range {
  return { file, line: fn.line, column: 1, end_line: fn.endLine, end_column: 1 };
}

function fnItemId(unit: Unit, fn: string): string {
  return `${unit.id}::${fn}`;
}

/// The findings of a unit with their files resolved; one outside the user's files (the injected
/// std.rs) goes to the start of the unit's file.
function unitFindings(unit: Unit): report.Finding[] {
  const fallback = { file: unit.file, line: 1, column: 1 };
  return report
    .findings(unit.report, unit.diagnostics, unit.outcome, fallback)
    .map((f) => report.resolveFinding(f, unit.root, unit.cwd))
    .map((f) => (fs.existsSync(f.location.file) ? f : atStart(f, unit.file)));
}

/// The verdict of several crates: unsafe when one is, then error, then unknown; error when no
/// crate was checked.
function overallVerdict(verdicts: report.Verdict[]): report.Verdict {
  const order: report.Verdict[] = ["unsafe", "error", "unknown"];
  return order.find((v) => verdicts.includes(v)) ?? (verdicts.length > 0 ? "safe" : "error");
}

function unitStatus(verdict: report.Verdict): report.Status {
  return verdict === "safe" ? "pass" : verdict === "unsafe" ? "fail" : "unknown";
}

/// A passing function passes, a failing one fails, and one the run decides neither way is
/// errored: the run could not give it a verdict.
function setState(testRun: vscode.TestRun, item: vscode.TestItem, status: report.Status, messages: vscode.TestMessage[]): void {
  if (status === "pass") {
    testRun.passed(item);
  } else if (status === "fail") {
    testRun.failed(item, messages);
  } else {
    testRun.errored(item, messages);
  }
}

/// A message per refutation at its span, or the result's message.
function resultMessages(result: report.FunctionResult, unit: Unit): vscode.TestMessage[] {
  const lines = new Lines();
  const located = result.failures.flatMap((failure) => {
    const location = report.locationOf(failure.span);
    if (!location) {
      return [];
    }
    const resolved = report.resolveLocation(location, unit.root);
    const values = failure.values.length > 0 ? ` with ${report.formatValues(failure.values)}` : "";
    const message = new vscode.TestMessage(`refuted: ${failure.obligation ?? "obligation"}${values}`);
    message.location = new vscode.Location(vscode.Uri.file(resolved.file), toRange(resolved, lines));
    return [message];
  });
  return located.length > 0 ? located : [new vscode.TestMessage(result.message)];
}

function atStart(finding: report.Finding, file: string): report.Finding {
  const { file: original, line, column } = finding.location;
  return {
    ...finding,
    location: { file, line: 1, column: 1 },
    message: `${finding.message}\n(at ${path.basename(original)}:${line}:${column})`,
  };
}

/// The lines of the files the findings point into, read once per run.
class Lines {
  private readonly files = new Map<string, string[]>();

  /// The text of the 0-based `line` of `file`, empty when there is none.
  text(file: string, line: number): string {
    let lines = this.files.get(file);
    if (!lines) {
      lines = readLines(file);
      this.files.set(file, lines);
    }
    return lines[line] ?? "";
  }
}

function readLines(file: string): string[] {
  try {
    return fs.readFileSync(file, "utf8").split("\n");
  } catch {
    return [];
  }
}

/// The editor's range of a location, its columns turned from characters into UTF-16 units.
function toRange(location: report.Location, lines: Lines): vscode.Range {
  const line = Math.max(location.line - 1, 0);
  const text = lines.text(location.file, line);
  const start = report.utf16Column(text, location.column) - 1;
  if (location.endLine !== undefined && location.endColumn !== undefined) {
    const endLine = Math.max(location.endLine - 1, 0);
    const end = report.utf16Column(lines.text(location.file, endLine), location.endColumn) - 1;
    return new vscode.Range(line, start, endLine, end);
  }
  // A start only (a function's or a loop's start, a zero-width span):
  // the range runs to the end of the line, or covers the line when the start is at its end.
  return new vscode.Range(line, start < text.length ? start : 0, line, text.length);
}

function toDiagnostic(finding: report.Finding, lines: Lines): vscode.Diagnostic {
  const severity = {
    error: vscode.DiagnosticSeverity.Error,
    warning: vscode.DiagnosticSeverity.Warning,
    information: vscode.DiagnosticSeverity.Information,
  }[finding.severity];
  const diagnostic = new vscode.Diagnostic(toRange(finding.location, lines), finding.message, severity);
  diagnostic.source = finding.source;
  diagnostic.relatedInformation = finding.related.map(
    (r) =>
      new vscode.DiagnosticRelatedInformation(
        new vscode.Location(vscode.Uri.file(r.location.file), toRange(r.location, lines)),
        r.message,
      ),
  );
  return diagnostic;
}
