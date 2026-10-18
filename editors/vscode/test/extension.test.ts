// The compiled extension under the VS Code stub (test/vscode-stub.js), on a copy of the fixture
// workspace with cargo replaced by test/fake-cargo.js replaying the captured checks: what the
// Testing view and the diagnostics show after a run of the workspace, a run of one function, a
// run that does not reach a crate, and a run that gives no report.

import * as assert from "assert";
import * as fs from "fs";
import * as os from "os";
import * as path from "path";
import { test } from "node:test";

const here = path.join(__dirname, "..", "..");
const fixtures = path.join(here, "test", "fixtures", "cargo");

// The extension's `import * as vscode from "vscode"` resolves to the stub.
// eslint-disable-next-line @typescript-eslint/no-var-requires
const Module = require("module");
const resolve = Module._resolveFilename;
Module._resolveFilename = function (request: string, ...rest: unknown[]) {
  return request === "vscode" ? path.join(here, "test", "vscode-stub.js") : resolve.call(this, request, ...rest);
};
// eslint-disable-next-line @typescript-eslint/no-var-requires
const vscode = require("vscode");
// eslint-disable-next-line @typescript-eslint/no-var-requires
const extension = require("../src/extension");

interface State {
  state: string;
  id: string;
  messages: string[];
}

interface Thrust {
  verify(document: unknown, fn?: unknown): Promise<string | undefined>;
}

/// Waits until `condition` holds, checking every 20 ms, for at most 10 s.
async function until(condition: () => boolean): Promise<void> {
  const deadline = Date.now() + 10000;
  while (!condition()) {
    assert.ok(Date.now() < deadline, "timed out");
    await new Promise((resolve) => setTimeout(resolve, 20));
  }
}

interface Session {
  workspace: string;
  thrust: Thrust;
  /// Replays the captured case `name` (or a directory) at the next cargo check.
  replay(name: string): void;
  /// The arguments of each cargo call so far.
  calls(): string[];
  document(relative: string, dirty?: boolean): unknown;
  lens(relative: string, name: string): unknown;
  /// The states of the last test run, by item id relative to the workspace.
  states(): Map<string, State>;
  /// The diagnostics' first lines, `file:line message`.
  diagnostics(): string[];
  children(rootSuffix: string): string[];
}

function session(): Session {
  const workspace = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-extension-"));
  fs.cpSync(path.join(fixtures, "workspace"), workspace, { recursive: true });
  const log = path.join(workspace, "cargo.log");
  vscode.__reset();
  const s = vscode.__state;
  s.folder = workspace;
  const replay = (name: string) => {
    s.config = { command: ["thrust-rustc"], cargoCommand: [process.execPath, path.join(here, "test", "fake-cargo.js"), path.isAbsolute(name) ? name : path.join(fixtures, name)] };
  };
  replay("check");
  process.env.FAKE_WORKSPACE = workspace;
  process.env.FAKE_LOG = log;
  const context = { subscriptions: [] as unknown[], asAbsolutePath: (p: string) => path.join(here, p) };
  extension.activate(context);
  const relative = (id: string) => id.split(workspace).join("");
  return {
    workspace,
    thrust: context.subscriptions[0] as Thrust,
    replay,
    calls: () => (fs.existsSync(log) ? fs.readFileSync(log, "utf8").trim().split("\n") : []),
    document: (file, dirty = false) => vscode.__document(path.join(workspace, file), dirty),
    lens: (file, name) => {
      const lenses = s.providers.lens.provideCodeLenses(vscode.__document(path.join(workspace, file)));
      const lens = lenses.find((l: { command: { arguments: { name: string }[] } }) => l.command.arguments[1].name === name);
      assert.ok(lens, name);
      return lens.command.arguments[1];
    },
    states: () => {
      const run = s.runs[s.runs.length - 1];
      return new Map(run.states.filter((x: State) => x.state !== "started").map((x: State) => [relative(x.id), { ...x, id: relative(x.id) }]));
    },
    diagnostics: () =>
      [...s.diagnostics.entries()].flatMap(([file, list]: [string, { range: { start: { line: number } }; message: string }[]]) =>
        list.map((d) => `${path.relative(workspace, file)}:${d.range.start.line + 1} ${d.message.split("\n")[0]}`),
      ),
    children: (rootSuffix) => {
      let found: string[] = [];
      s.controller.items.forEach((root: { id: string; children: { forEach(f: (c: { label: string }) => void): void } }) => {
        if (root.id.endsWith(rootSuffix)) {
          found = [];
          root.children.forEach((c) => found.push(c.label));
        }
      });
      return found;
    },
  };
}

function stateOf(states: Map<string, State>, id: string): string | undefined {
  return states.get(id)?.state;
}

test("a run of the workspace: an item per crate with its verdict, its functions under it, the refutation as a diagnostic", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  const states = t.states();
  assert.strictEqual(stateOf(states, "#arith/lib/arith"), "passed");
  assert.strictEqual(stateOf(states, "#arith/lib/arith::<Pair as Scale>::scale"), "passed");
  assert.strictEqual(stateOf(states, "#app/bin/app"), "failed");
  assert.strictEqual(stateOf(states, "#app/bin/app::shrink"), "failed");
  assert.deepStrictEqual(t.diagnostics(), ["app/src/main.rs:9 refuted: ensures in `shrink`"]);
});

test("a crate the run does not reach is skipped with its functions, not left passing", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  t.replay("only");
  await t.thrust.verify(t.document("arith/src/lib.rs"));
  const states = t.states();
  assert.strictEqual(stateOf(states, "#arith/lib/arith"), "passed");
  assert.strictEqual(stateOf(states, "#app/bin/app"), "skipped");
  assert.strictEqual(stateOf(states, "#app/bin/app::shrink"), "skipped");
  assert.strictEqual(stateOf(states, "#both/lib/both"), "skipped");
  // The run's diagnostics replace those of the workspace's last run.
  assert.deepStrictEqual(t.diagnostics(), []);
});

test("a run of one function updates its item, found by its lines, and only the diagnostics on its lines", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  const before = t.children("#arith/lib/arith");
  t.replay("only");
  await t.thrust.verify(t.document("arith/src/lib.rs"), t.lens("arith/src/lib.rs", "scale"));
  const states = t.states();
  assert.deepStrictEqual([...states.keys()], ["#arith/lib/arith::<Pair as Scale>::scale"]);
  assert.strictEqual(stateOf(states, "#arith/lib/arith::<Pair as Scale>::scale"), "passed");
  assert.deepStrictEqual(t.children("#arith/lib/arith"), before);
  assert.deepStrictEqual(t.diagnostics(), ["app/src/main.rs:9 refuted: ensures in `shrink`"]);
  const last = t.calls()[t.calls().length - 1];
  assert.match(last, /check --message-format=json --manifest-path \S+ -p arith --lib$/);
});

test("a run of one function without a report to read: its item errored with why, its old diagnostics kept, the error shown", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  const failed = path.join(t.workspace, "selects-nothing");
  fs.mkdirSync(failed);
  const message = { message: "`THRUST_VERIFY_ONLY` entry `shrink` selects no function", level: "error", spans: [], children: [] };
  const target = { kind: ["bin"], crate_types: ["bin"], name: "app", src_path: "/workspace/app/src/main.rs" };
  fs.writeFileSync(path.join(failed, "stdout.jsonl"), `${JSON.stringify({ reason: "compiler-message", target, message })}\n`);
  fs.writeFileSync(path.join(failed, "exit"), "101\n");
  fs.copyFileSync(path.join(fixtures, "metadata.json"), path.join(t.workspace, "metadata.json"));
  t.replay(failed);
  await t.thrust.verify(t.document("app/src/main.rs"), t.lens("app/src/main.rs", "shrink"));
  const states = t.states();
  assert.strictEqual(states.get("#app/bin/app::shrink")?.state, "errored");
  assert.match(states.get("#app/bin/app::shrink")?.messages[0] ?? "", /selects no function/);
  assert.deepStrictEqual(t.diagnostics().sort(), [
    "app/src/main.rs:1 Thrust: error (`THRUST_VERIFY_ONLY` entry `shrink` selects no function)",
    "app/src/main.rs:9 refuted: ensures in `shrink`",
  ]);
});

const checks = (t: Session) => t.calls().filter((c) => c.startsWith("check")).length;

test("no run while a Rust file of the workspace has unsaved changes", async () => {
  const t = session();
  t.document("arith/src/ops.rs", true);
  assert.match((await t.thrust.verify(t.document("app/src/main.rs"))) ?? "", /ops.rs has unsaved changes/);
  assert.strictEqual(checks(t), 0);
  assert.match(vscode.__state.warnings[0], /unsaved changes/);
});

test("a run's result is not shown when a file of the workspace changed during it", async () => {
  const t = session();
  const hold = path.join(t.workspace, "hold");
  process.env.FAKE_HOLD = hold;
  try {
    const lib = t.document("arith/src/lib.rs") as { version: number };
    const running = t.thrust.verify(t.document("app/src/main.rs"));
    await until(() => checks(t) === 1);
    // An edit saved during the run, so the document is not dirty, but of another version.
    lib.version += 1;
    fs.writeFileSync(hold, "");
    assert.match((await running) ?? "", /lib.rs changed during the run/);
    assert.strictEqual(vscode.__state.runs.length, 0);
    assert.deepStrictEqual(t.diagnostics(), []);
  } finally {
    delete process.env.FAKE_HOLD;
  }
});

test("a document opened during a run, without changes, does not drop its result", async () => {
  const t = session();
  const hold = path.join(t.workspace, "hold");
  process.env.FAKE_HOLD = hold;
  try {
    const running = t.thrust.verify(t.document("app/src/main.rs"));
    await until(() => checks(t) === 1);
    t.document("arith/src/ops.rs");
    fs.writeFileSync(hold, "");
    assert.strictEqual(await running, undefined);
    assert.deepStrictEqual(t.diagnostics(), ["app/src/main.rs:9 refuted: ensures in `shrink`"]);
  } finally {
    delete process.env.FAKE_HOLD;
  }
});

test("saving a file and starting a run invalidate the results they make outdated", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  vscode.__state.config.verifyOnSave = false;
  vscode.__state.onSave(t.document("arith/src/ops.rs"));
  // Every crate of the workspace: a crate may use the one saved.
  assert.deepStrictEqual(
    vscode.__state.invalidated.map((id: string) => id.split(t.workspace).join("")),
    ["#arith/lib/arith", "#app/bin/app", "#both/lib/both", "#both/bin/both"],
  );
  vscode.__state.invalidated.length = 0;
  t.replay("only");
  await t.thrust.verify(t.document("arith/src/lib.rs"), t.lens("arith/src/lib.rs", "scale"));
  assert.deepStrictEqual(vscode.__state.invalidated.map((id: string) => id.split(t.workspace).join("")), ["#arith/lib/arith::<Pair as Scale>::scale"]);
});

test("a run stopped from the Testing view errs its items, left invalidated", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  const hold = path.join(t.workspace, "hold");
  process.env.FAKE_HOLD = hold;
  try {
    let cancel = () => {};
    const onCancellationRequested = (f: () => void) => {
      cancel = f;
      return { dispose() {} };
    };
    let root: unknown;
    vscode.__state.controller.items.forEach((item: { id: string }) => (root = item.id.endsWith("#app/bin/app") ? item : root));
    vscode.__state.invalidated.length = 0;
    const running = vscode.__state.profile(new vscode.TestRunRequest([root]), { isCancellationRequested: false, onCancellationRequested });
    await until(() => checks(t) === 2);
    // The run of the crate's item invalidated the workspace's results at its start.
    assert.deepStrictEqual(
      vscode.__state.invalidated.map((id: string) => id.split(t.workspace).join("")),
      ["#arith/lib/arith", "#app/bin/app", "#both/lib/both", "#both/bin/both"],
    );
    cancel();
    await running;
    assert.match(vscode.__state.status.text, /Thrust: unknown/);
    const states = t.states();
    assert.strictEqual(states.get("#app/bin/app")?.state, "errored");
    assert.deepStrictEqual(states.get("#app/bin/app")?.messages, ["stopped"]);
  } finally {
    delete process.env.FAKE_HOLD;
  }
});

test("a function's run shows the function's status in the status bar, not the crate's", async () => {
  const t = session();
  t.replay("only");
  // The replayed check selected `Pair::scale`: `inc`'s body was not checked, though the crate is sat.
  await t.thrust.verify(t.document("arith/src/lib.rs"), t.lens("arith/src/lib.rs", "inc"));
  assert.strictEqual(vscode.__state.status.text, "$(question) Thrust: unknown");
  assert.strictEqual(t.states().get("#arith/lib/arith::inc")?.state, "skipped");
  let inc: { description?: string } | undefined;
  vscode.__state.controller.items.forEach((root: { children: { forEach(f: (c: { label: string; description?: string }) => void): void } }) =>
    root.children.forEach((c) => (inc = c.label === "inc" ? c : inc)),
  );
  assert.strictEqual(inc?.description, "unselected: outside THRUST_VERIFY_ONLY, its written contract assumed");
  await t.thrust.verify(t.document("arith/src/lib.rs"), t.lens("arith/src/lib.rs", "scale"));
  assert.strictEqual(vscode.__state.status.text, "$(pass) Thrust: safe");
});

test("running all items from the Testing view checks the workspace once", async () => {
  const t = session();
  await t.thrust.verify(t.document("app/src/main.rs"));
  assert.strictEqual(checks(t), 1);
  await vscode.__state.profile(new vscode.TestRunRequest(undefined), { isCancellationRequested: false, onCancellationRequested: () => ({ dispose() {} }) });
  assert.strictEqual(checks(t), 2);
});

/// A session on a folder without Cargo.toml holding `file` of the fixtures, Thrust replaced by
/// test/fake-thrust.js replaying the captured case `name`.
function fileSession(file: string): { thrust: Thrust; folder: string; replay(name: string): void } {
  const folder = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-extension-"));
  fs.copyFileSync(path.join(here, "test", "fixtures", file), path.join(folder, file));
  vscode.__reset();
  const s = vscode.__state;
  s.folder = folder;
  const replay = (name: string) => {
    s.config = { command: [process.execPath, path.join(here, "test", "fake-thrust.js"), path.join(here, "test", "fixtures", name)], extraArgs: [] };
  };
  const context = { subscriptions: [] as unknown[], asAbsolutePath: (p: string) => path.join(here, p) };
  extension.activate(context);
  return { thrust: context.subscriptions[0] as Thrust, folder, replay };
}

test("a function's run does not put its status on the item of a function nested in it", async () => {
  const t = fileSession("nested.rs");
  const file = path.join(t.folder, "nested.rs");
  t.replay("only-nested-split");
  await t.thrust.verify(vscode.__document(file));
  const lenses = vscode.__state.providers.lens.provideCodeLenses(vscode.__document(file));
  const outer = lenses.find((l: { command: { arguments: { name: string }[] } }) => l.command.arguments[1].name === "outer").command.arguments[1];
  await t.thrust.verify(vscode.__document(file), outer);
  const run = vscode.__state.runs[vscode.__state.runs.length - 1];
  assert.deepStrictEqual(
    run.states.map((x: State) => [x.state, x.id.split(t.folder).join("")]),
    [["skipped", "/nested.rs::outer"]],
  );
});

test("the item of a function defined inside another errs instead of running the outer one", async () => {
  const t = fileSession("nested.rs");
  t.replay("only-nested-split");
  await t.thrust.verify(vscode.__document(path.join(t.folder, "nested.rs")));
  let inner: unknown;
  vscode.__state.controller.items.forEach((root: { children: { forEach(f: (c: { label: string }) => void): void } }) =>
    root.children.forEach((c) => (inner = c.label === "outer::inner" ? c : inner)),
  );
  const runs = vscode.__state.runs.length;
  await vscode.__state.profile(new vscode.TestRunRequest([inner]), { isCancellationRequested: false, onCancellationRequested: () => ({ dispose() {} }) });
  assert.strictEqual(vscode.__state.runs.length, runs + 1);
  const states = vscode.__state.runs[runs].states.filter((x: State) => x.state !== "started");
  assert.deepStrictEqual(states.map((x: State) => [x.state, x.messages[0]]), [["errored", "defined inside `outer`: run that function"]]);
});

test("a function's run whose report can be read replaces rustc's diagnostics in its crate", async () => {
  const t = session();
  const broken = path.join(t.workspace, "broken");
  fs.mkdirSync(broken);
  const span = { file_name: "arith/src/lib.rs", line_start: 2, line_end: 2, column_start: 1, column_end: 2, is_primary: true, label: null };
  const message = { message: "an error rustc gave", level: "error", spans: [span], children: [] };
  const target = { kind: ["lib"], crate_types: ["lib"], name: "arith", src_path: "/workspace/arith/src/lib.rs" };
  fs.writeFileSync(path.join(broken, "stdout.jsonl"), `${JSON.stringify({ reason: "compiler-message", manifest_path: "/workspace/arith/Cargo.toml", target, message })}\n`);
  fs.writeFileSync(path.join(broken, "exit"), "101\n");
  fs.copyFileSync(path.join(fixtures, "metadata.json"), path.join(t.workspace, "metadata.json"));
  t.replay(broken);
  await t.thrust.verify(t.document("arith/src/lib.rs"));
  assert.deepStrictEqual(t.diagnostics(), ["arith/src/lib.rs:2 an error rustc gave"]);
  t.replay("only");
  await t.thrust.verify(t.document("arith/src/lib.rs"), t.lens("arith/src/lib.rs", "scale"));
  assert.deepStrictEqual(t.diagnostics(), []);
});
