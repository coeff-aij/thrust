// Running Thrust on one file with the JSON report, and collecting what the run leaves. Nothing
// here depends on VS Code.

import { spawn } from "child_process";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";

export interface RunConfig {
  /// The program and its leading arguments.
  command: string[];
  extraArgs: string[];
  env: Record<string, string>;
  /// THRUST_SPLIT; 0 solves one query.
  split: number;
  /// THRUST_CACHE_DIR, absolute; empty keeps nothing.
  cacheDir: string;
  timeoutSecs: number;
}

export interface Invocation {
  program: string;
  args: string[];
  /// The variables the run sets on top of the inherited environment.
  env: Record<string, string>;
  cwd: string;
  reportFile: string;
}

export interface RunResult {
  invocation: Invocation;
  exitCode: number | null;
  stderr: string;
  report: string;
  timedOut: boolean;
  cancelled: boolean;
  durationMs: number;
}

/// What a run of `file` executes, with its output in `scratch`. The file is passed relative to
/// its directory, where the run starts, so the report's spans name it as the editor does after
/// resolving them against that directory.
export function invocation(file: string, config: RunConfig, scratch: string): Invocation {
  const [program, ...leading] = config.command;
  if (!program) {
    throw new Error("thrust.command is empty");
  }
  const reportFile = path.join(scratch, "report.jsonl");
  const env: Record<string, string> = {
    ...config.env,
    THRUST_REPORT: "1",
    THRUST_REPORT_FORMAT: "json",
    THRUST_REPORT_FILE: reportFile,
  };
  if (config.split > 0) {
    env.THRUST_SPLIT = String(config.split);
  }
  if (config.cacheDir !== "") {
    env.THRUST_CACHE_DIR = config.cacheDir;
  }
  const args = [...leading, ...config.extraArgs, "--error-format=json", "--out-dir", scratch, path.basename(file)];
  return { program, args, env, cwd: path.dirname(file), reportFile };
}

/// Runs Thrust on `file`; `signal` stops it (a newer run of the same file).
export async function run(file: string, config: RunConfig, signal?: AbortSignal): Promise<RunResult> {
  const scratch = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-vscode-"));
  try {
    const inv = invocation(file, config, scratch);
    const started = Date.now();
    const outcome = await execute(inv, config.timeoutSecs, signal);
    return {
      invocation: inv,
      ...outcome,
      report: readIfPresent(inv.reportFile),
      durationMs: Date.now() - started,
    };
  } finally {
    fs.rmSync(scratch, { recursive: true, force: true });
  }
}

interface Execution {
  exitCode: number | null;
  stderr: string;
  timedOut: boolean;
  cancelled: boolean;
}

function execute(inv: Invocation, timeoutSecs: number, signal?: AbortSignal): Promise<Execution> {
  return new Promise((resolve) => {
    const child = spawn(inv.program, inv.args, {
      cwd: inv.cwd,
      env: { ...process.env, ...inv.env },
      stdio: ["ignore", "ignore", "pipe"],
    });
    let stderr = "";
    let timedOut = false;
    let cancelled = false;
    const stop = () => child.kill("SIGTERM");
    const timer = setTimeout(() => {
      timedOut = true;
      stop();
    }, timeoutSecs * 1000);
    const onAbort = () => {
      cancelled = true;
      stop();
    };
    signal?.addEventListener("abort", onAbort);
    child.stderr.on("data", (chunk: Buffer) => (stderr += chunk.toString("utf8")));
    const finish = (exitCode: number | null, extra = "") => {
      clearTimeout(timer);
      signal?.removeEventListener("abort", onAbort);
      resolve({ exitCode, stderr: stderr + extra, timedOut, cancelled });
    };
    child.on("error", (err) => finish(null, `${err.message}\n`));
    child.on("close", (code) => finish(code));
  });
}

function readIfPresent(file: string): string {
  try {
    return fs.readFileSync(file, "utf8");
  } catch {
    return "";
  }
}
