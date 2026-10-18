// The VS Code side: runs Thrust on a Rust file (on command or on save) and shows the run's
// findings as diagnostics, its inferred contracts and counterexample facts as inlay hints and
// hovers, and its verdict in the status bar.

import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";
import * as report from "./report";
import { run, RunConfig, RunResult } from "./runner";


export function activate(context: vscode.ExtensionContext): void {
  const thrust = new Thrust();
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
    vscode.commands.registerCommand("thrust.showOutput", () => thrust.output.show()),
    vscode.workspace.onDidSaveTextDocument((document) => {
      if (document.languageId === "rust" && settings(document).get<boolean>("verifyOnSave", true)) {
        void thrust.verify(document);
      }
    }),
    vscode.languages.registerInlayHintsProvider({ language: "rust" }, thrust),
    vscode.languages.registerHoverProvider({ language: "rust" }, thrust),
  );
}

export function deactivate(): void {}

function settings(document: vscode.TextDocument): vscode.WorkspaceConfiguration {
  return vscode.workspace.getConfiguration("thrust", document.uri);
}

function runConfig(document: vscode.TextDocument): RunConfig {
  const config = settings(document);
  const folder = vscode.workspace.getWorkspaceFolder(document.uri)?.uri.fsPath ?? path.dirname(document.uri.fsPath);
  const cacheDir = config.get<string>("cacheDir", "");
  return {
    command: config.get<string[]>("command", ["thrust-rustc"]),
    extraArgs: config.get<string[]>("extraArgs", []),
    env: config.get<Record<string, string>>("env", {}),
    split: config.get<number>("split", 0),
    cacheDir: cacheDir === "" ? "" : path.resolve(folder, cacheDir),
    timeoutSecs: config.get<number>("timeoutSecs", 300),
  };
}

class Thrust implements vscode.InlayHintsProvider, vscode.HoverProvider, vscode.Disposable {
  readonly output = vscode.window.createOutputChannel("Thrust");
  private readonly diagnostics = vscode.languages.createDiagnosticCollection("thrust");
  private readonly status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 10);
  private readonly hintsChanged = new vscode.EventEmitter<void>();
  readonly onDidChangeInlayHints = this.hintsChanged.event;
  /// By file path: the hints of the last run, for the inlay hints and the hovers, and the run in
  /// progress.
  private readonly shown = new Map<string, report.Hint[]>();
  private readonly running = new Map<string, AbortController>();

  constructor() {
    this.status.command = "thrust.showOutput";
    this.status.text = "$(shield) Thrust";
    this.status.tooltip = "Thrust: not run yet";
    this.status.show();
  }

  dispose(): void {
    for (const controller of this.running.values()) {
      controller.abort();
    }
    this.output.dispose();
    this.diagnostics.dispose();
    this.status.dispose();
    this.hintsChanged.dispose();
  }

  async verify(document: vscode.TextDocument): Promise<void> {
    const file = document.uri.fsPath;
    this.running.get(file)?.abort();
    const controller = new AbortController();
    this.running.set(file, controller);
    this.status.text = "$(sync~spin) Thrust: verifying";
    this.status.tooltip = path.basename(file);
    let result: RunResult;
    try {
      result = await run(file, runConfig(document), controller.signal);
    } catch (err) {
      this.showStatus("error", String(err), file);
      return;
    }
    if (result.cancelled) {
      return;
    }
    this.running.delete(file);
    this.log(result);
    this.show(document, result);
  }

  private log(result: RunResult): void {
    const inv = result.invocation;
    const env = Object.entries(inv.env)
      .map(([k, v]) => `${k}=${v}`)
      .join(" ");
    this.output.appendLine(`$ cd ${inv.cwd} && ${env} ${inv.program} ${inv.args.join(" ")}`);
    this.output.appendLine(`exit ${result.exitCode}${result.timedOut ? " (stopped at the time limit)" : ""}, ${result.durationMs} ms`);
    if (result.stderr.trim() !== "") {
      this.output.appendLine(result.stderr.trimEnd());
    }
  }

  private show(document: vscode.TextDocument, result: RunResult): void {
    const cwd = result.invocation.cwd;
    const parsed = report.parseReport(result.report);
    const { diagnostics } = report.parseDiagnostics(result.stderr);
    const outcome = result.timedOut
      ? { verdict: "unknown" as const, detail: "stopped at thrust.timeoutSecs" }
      : report.verdictOf(result.exitCode, parsed, diagnostics);
    const fallback = { file: document.uri.fsPath, line: 1, column: 1 };
    const root = report.reportRoot(parsed, cwd);
    const findings = report.findings(parsed, diagnostics, outcome, fallback).map((f) => report.resolveFinding(f, root, cwd));
    const hints = report.hints(parsed).map((h) => ({ ...h, location: report.resolveLocation(h.location, root) }));
    this.publish(findings, hints, document.uri.fsPath);
    this.showStatus(outcome.verdict, outcome.detail, document.uri.fsPath);
  }

  private publish(findings: report.Finding[], hints: report.Hint[], file: string): void {
    this.diagnostics.clear();
    this.shown.clear();
    const byFile = new Map<string, report.Finding[]>();
    for (const found of findings) {
      // A span outside the user's files (the injected std.rs) goes to the verified file's start.
      const finding = fs.existsSync(found.location.file) ? found : atStart(found, file);
      const target = finding.location.file;
      byFile.set(target, [...(byFile.get(target) ?? []), finding]);
    }
    const lines = new Lines();
    for (const [target, list] of byFile) {
      this.diagnostics.set(
        vscode.Uri.file(target),
        list.map((f) => toDiagnostic(f, lines)),
      );
    }
    for (const hint of hints) {
      this.shown.set(hint.location.file, [...(this.shown.get(hint.location.file) ?? []), hint]);
    }
    this.hintsChanged.fire();
  }

  private showStatus(verdict: report.Verdict, detail: string, file: string): void {
    const icon = { safe: "$(pass)", unsafe: "$(error)", unknown: "$(question)", error: "$(warning)" }[verdict];
    this.status.text = `${icon} Thrust: ${verdict}`;
    this.status.tooltip = `${path.basename(file)}: ${detail}\nClick for the output of the run.`;
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
