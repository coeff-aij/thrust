// Running Thrust on a cargo workspace: `cargo check` with `RUSTC` set to bin/thrust-rustc-cargo,
// which runs Thrust on each crate and writes a JSON report per crate of the workspace, and reading
// cargo's messages, its metadata and the reports. Nothing here depends on VS Code.

import * as fs from "fs";
import * as path from "path";
import { Outcome, Report, RustcDiagnostic, verdictOf } from "./report";
import { Command, execute, readIfPresent, RunConfig, thrustEnv } from "./runner";

/// The separator of the words of a list passed to the wrapper in one variable.
const SEPARATOR = "\x1f";

export interface CargoConfig extends RunConfig {
  /// The program running cargo and its leading arguments.
  cargo: string[];
}

export interface CargoInvocation extends Command {
  /// Where the crates' reports are.
  reportDir: string;
}

export interface Target {
  /// The package's name, the target's name and kind (`lib`, `bin`, `proc-macro`, ...).
  package: string;
  name: string;
  kind: string;
  crateType: string;
  srcPath: string;
  /// The package's Cargo.toml, which cargo's messages name.
  manifestPath: string;
}

export interface Metadata {
  workspaceRoot: string;
  targetDirectory: string;
  /// The lib and bin targets of the workspace's packages, the ones `cargo check` checks.
  targets: Target[];
}

/// The targets `cargo check` checks: a library (of any crate type) or a binary.
const CHECKED_KINDS = new Set(["lib", "rlib", "dylib", "cdylib", "staticlib", "proc-macro", "bin"]);

/// Reads the output of `cargo metadata --no-deps --format-version 1`.
export function parseMetadata(text: string): Metadata {
  const json = JSON.parse(text) as {
    workspace_root: string;
    target_directory: string;
    workspace_members: string[];
    packages: { id: string; name: string; manifest_path: string; targets: MessageTarget[] }[];
  };
  const members = new Set(json.workspace_members);
  const targets = json.packages
    .filter((p) => members.has(p.id))
    .flatMap((p) =>
      p.targets
        .filter((t) => CHECKED_KINDS.has(t.kind[0]))
        .map((t) => targetFrom(p.name, p.manifest_path, t)),
    );
  return { workspaceRoot: json.workspace_root, targetDirectory: json.target_directory, targets };
}

/// A target as cargo's metadata and messages give it.
interface MessageTarget {
  name: string;
  kind: string[];
  crate_types: string[];
  src_path: string;
}

function targetFrom(pkg: string, manifestPath: string, t: MessageTarget): Target {
  return { package: pkg, name: t.name, kind: t.kind[0], crateType: t.crate_types[0], srcPath: t.src_path, manifestPath };
}

/// The target `file` belongs to: the one whose root file it is, else the one whose root's
/// directory is the nearest above it, a library before a binary there. A module file shared by
/// a library and a binary in one directory is taken as the library's.
export function targetOf(file: string, metadata: Metadata): Target | undefined {
  const resolved = path.resolve(file);
  const exact = metadata.targets.find((t) => path.resolve(t.srcPath) === resolved);
  if (exact) {
    return exact;
  }
  const above = metadata.targets.filter((t) => isInside(resolved, path.dirname(t.srcPath)));
  const depth = (t: Target) => path.dirname(t.srcPath).length;
  return above.sort((a, b) => depth(b) - depth(a) || Number(a.kind === "bin") - Number(b.kind === "bin"))[0];
}

function isInside(file: string, dir: string): boolean {
  const relative = path.relative(dir, file);
  return relative !== "" && !relative.startsWith("..") && !path.isAbsolute(relative);
}

/// The name of a crate's report as bin/thrust-rustc-cargo writes it.
export function reportFileName(target: Target): string {
  return `${target.package}.${crateName(target)}.${target.crateType}.jsonl`;
}

/// The directory cargo builds into for Thrust, apart from the workspace's own builds, as Kani
/// (`target/kani`) and Flux (`target/flux`) do, and the reports' directory in it.
export function thrustTargetDir(metadata: Metadata): string {
  return path.join(metadata.targetDirectory, "thrust");
}

export function reportDir(metadata: Metadata): string {
  return path.join(thrustTargetDir(metadata), "reports");
}

/// What a check executes: the whole workspace, or with `only` the one target, whose crate the
/// wrapper runs with `THRUST_VERIFY_ONLY` set to the selection.
export function cargoInvocation(
  metadata: Metadata,
  config: CargoConfig,
  wrapper: string,
  only?: { target: Target; selection: string },
): CargoInvocation {
  const [program, ...leading] = config.cargo;
  if (!program) {
    throw new Error("thrust.cargoCommand is empty");
  }
  const env: Record<string, string> = {
    ...thrustEnv(config),
    RUSTC: wrapper,
    RUSTC_WRAPPER: "",
    RUSTC_WORKSPACE_WRAPPER: "",
    CARGO_TARGET_DIR: thrustTargetDir(metadata),
    THRUST_VSCODE_COMMAND: config.command.join(SEPARATOR),
    THRUST_VSCODE_ARGS: config.extraArgs.join(SEPARATOR),
    THRUST_VSCODE_THRUST_ID: commandIdentity(config.command, metadata.workspaceRoot),
    THRUST_VSCODE_ENV_KEYS: Object.keys(config.env).join(SEPARATOR),
    THRUST_VSCODE_REPORT_DIR: reportDir(metadata),
  };
  const manifest = path.join(metadata.workspaceRoot, "Cargo.toml");
  const args = [...leading, "check", "--message-format=json", "--manifest-path", manifest];
  if (only) {
    env.THRUST_VSCODE_VERIFY_ONLY = only.selection;
    env.THRUST_VSCODE_VERIFY_CRATE = `${crateName(only.target)}.${only.target.crateType}`;
    args.push("-p", only.target.package, ...targetArgs(only.target));
  } else {
    args.push("--workspace", "--keep-going");
  }
  return { program, args, env, cwd: metadata.workspaceRoot, reportDir: reportDir(metadata) };
}

/// What tells builds of the command apart: each of its words that names a file (the Thrust
/// binary; the program found on PATH; a relative path against `cwd`), with the file's path,
/// size and modification time.
export function commandIdentity(command: string[], cwd: string): string {
  return command
    .flatMap((word, k) => {
      const file = k === 0 && !word.includes("/") ? onPath(word) : path.resolve(cwd, word);
      const stat = file === undefined ? undefined : statOf(file);
      return stat?.isFile() ? [`${file}:${stat.size}:${stat.mtimeMs}`] : [];
    })
    .join(SEPARATOR);
}

function onPath(program: string): string | undefined {
  const dirs = (process.env.PATH ?? "").split(path.delimiter).filter((d) => d !== "");
  return dirs.map((d) => path.join(d, program)).find((file) => statOf(file)?.isFile());
}

function statOf(file: string): fs.Stats | undefined {
  try {
    return fs.statSync(file);
  } catch {
    return undefined;
  }
}

function crateName(target: Target): string {
  return target.name.replace(/-/g, "_");
}

function targetArgs(target: Target): string[] {
  return target.kind === "bin" ? ["--bin", target.name] : ["--lib"];
}

/// What one crate of a check left: its report, if it wrote one, and rustc's diagnostics.
export interface CrateRun {
  target: Target;
  report: string;
  diagnostics: RustcDiagnostic[];
  /// Whether cargo compiled it (a `compiler-artifact`), so that it passed rustc and Thrust.
  compiled: boolean;
}

interface CargoMessage {
  reason: string;
  manifest_path?: string;
  target?: MessageTarget;
  message?: RustcDiagnostic;
}

/// The crates a check went through, from cargo's JSON messages, each with its diagnostics and,
/// from `reports`, the report of its run: of every crate, or of `only` when the check was of
/// that target, as the others ran as dependencies, without a report. A crate that is not a lib
/// or bin target of the workspace (a build script, a dependency) is one too, under its own
/// target.
export function crateRuns(stdout: string, metadata: Metadata, reports: string, only?: Target): CrateRun[] {
  const runs = new Map<string, CrateRun>();
  for (const message of cargoMessages(stdout)) {
    if (!message.target || (message.reason !== "compiler-message" && message.reason !== "compiler-artifact")) {
      continue;
    }
    const target = findTarget(metadata, message.manifest_path, message.target);
    const run = runs.get(targetKey(target)) ?? { target, report: "", diagnostics: [], compiled: false };
    runs.set(targetKey(target), run);
    if (message.reason === "compiler-artifact") {
      run.compiled = true;
    } else if (message.message) {
      run.diagnostics.push(message.message);
    }
  }
  for (const run of runs.values()) {
    if (!only || targetKey(run.target) === targetKey(only)) {
      run.report = readIfPresent(path.join(reports, reportFileName(run.target)));
    }
  }
  return [...runs.values()];
}

const NOT_A_CRATE_ERROR = /^(verification error: |aborting due to )/;

/// The outcome of a crate: an error when cargo did not compile it for an error other than a
/// refutation (a compile error, a `THRUST_VERIFY_ONLY` entry selecting nothing), whatever its
/// report says, or when it did not compile it though its report is `sat`; otherwise the
/// report's.
export function crateOutcome(run: CrateRun, report: Report): Outcome {
  if (run.compiled) {
    return verdictOf(null, report, run.diagnostics);
  }
  const error = run.diagnostics.find((d) => d.level === "error" && !NOT_A_CRATE_ERROR.test(d.message));
  if (error) {
    return { verdict: "error", detail: error.message };
  }
  if (report.verdict?.verdict === "sat") {
    return { verdict: "error", detail: "cargo did not compile the crate, though its report is sat" };
  }
  return verdictOf(null, report, run.diagnostics);
}

/// The workspace's target a message is of, by its package's manifest, name and kind; another
/// target (a build script) as the message gives it.
function findTarget(metadata: Metadata, manifestPath: string | undefined, t: MessageTarget): Target {
  const kind = t.kind[0];
  const known = metadata.targets.find(
    (x) => x.name === t.name && x.kind === kind && (manifestPath === undefined || x.manifestPath === manifestPath),
  );
  const pkg = metadata.targets.find((x) => x.manifestPath === manifestPath)?.package ?? t.name;
  return known ?? targetFrom(pkg, manifestPath ?? "", t);
}

/// What tells targets apart: a package's lib and bin of one name, two packages' bins of one name.
export function targetKey(target: Target): string {
  return `${target.manifestPath}#${target.kind}#${target.name}`;
}

function cargoMessages(stdout: string): CargoMessage[] {
  const messages: CargoMessage[] = [];
  for (const line of stdout.split("\n")) {
    try {
      const value: unknown = JSON.parse(line);
      if (typeof value === "object" && value !== null && "reason" in value) {
        messages.push(value as CargoMessage);
      }
    } catch {
      // Not a message: a line a build script printed.
    }
  }
  return messages;
}

export interface CargoResult {
  invocation: CargoInvocation;
  exitCode: number | null;
  /// cargo's own output: progress, and errors that are not a crate's.
  stderr: string;
  crates: CrateRun[];
  timedOut: boolean;
  cancelled: boolean;
  durationMs: number;
}

/// Reads the workspace's metadata with `cargo metadata`, from the directory `dir`.
export async function metadataOf(dir: string, cargo: string[], signal?: AbortSignal): Promise<Metadata> {
  const [program, ...leading] = cargo;
  const command: Command = { program, args: [...leading, "metadata", "--no-deps", "--format-version", "1"], env: {}, cwd: dir };
  const outcome = await execute(command, 60, signal);
  if (outcome.exitCode !== 0) {
    throw new Error(`cargo metadata failed (exit ${outcome.exitCode}): ${outcome.stderr.trim()}`);
  }
  return parseMetadata(outcome.stdout);
}

/// Checks the workspace, or one function of it with `only`.
export async function runCargo(
  metadata: Metadata,
  config: CargoConfig,
  wrapper: string,
  only?: { target: Target; selection: string },
  signal?: AbortSignal,
): Promise<CargoResult> {
  const inv = cargoInvocation(metadata, config, wrapper, only);
  fs.mkdirSync(inv.reportDir, { recursive: true });
  const started = Date.now();
  const outcome = await execute(inv, config.timeoutSecs, signal);
  return {
    invocation: inv,
    exitCode: outcome.exitCode,
    stderr: outcome.stderr,
    crates: crateRuns(outcome.stdout, metadata, inv.reportDir, only?.target),
    timedOut: outcome.timedOut,
    cancelled: outcome.cancelled,
    durationMs: Date.now() - started,
  };
}
