// Drives the compiled extension under the VS Code stub with a real thrust-rustc, on copies of the
// fixture workspace and of single-file fixtures (unsafe.rs, trusted.rs, nested.rs), and prints
// what it shows: the Testing view's states and the diagnostics after each step. Not part of
// `npm test`; it needs Thrust built, z3 and the toolchain.
//
// Usage: npm run compile && node test/drive-real.js <thrust-rustc> [split]
//   e.g. node test/drive-real.js /path/to/thrust/target/debug/thrust-rustc 2
const fs = require("fs");
const os = require("os");
const path = require("path");
const Module = require("module");

const here = path.join(__dirname, "..");
const resolve = Module._resolveFilename;
Module._resolveFilename = function (request, ...rest) {
  return request === "vscode" ? path.join(here, "test", "vscode-stub.js") : resolve.call(this, request, ...rest);
};
const vscode = require("vscode");
const extension = require(path.join(here, "out", "src", "extension.js"));

const [thrustRustc, split] = process.argv.slice(2);
if (!thrustRustc) {
  console.error("usage: node test/drive-real.js <thrust-rustc> [split]");
  process.exit(2);
}
const toolchain = "nightly-2025-09-08";
const s = vscode.__state;

/// Activates the extension on a copy of `source` (a directory or a file) as the workspace folder.
function start(source, cargo) {
  const folder = fs.mkdtempSync(path.join(os.tmpdir(), "thrust-drive-"));
  fs.cpSync(source, fs.statSync(source).isDirectory() ? folder : path.join(folder, path.basename(source)), { recursive: true });
  vscode.__reset();
  s.folder = folder;
  s.config = {
    command: cargo ? [thrustRustc] : ["rustup", "run", toolchain, thrustRustc],
    cargoCommand: ["cargo", `+${toolchain}`],
    extraArgs: ["-Awarnings", "-C", "debug-assertions=off"],
    split: Number(split ?? 0),
  };
  const context = { subscriptions: [], asAbsolutePath: (p) => path.join(here, p) };
  extension.activate(context);
  return { folder, thrust: context.subscriptions[0] };
}

const token = { isCancellationRequested: false, onCancellationRequested: () => ({ dispose() {} }) };

function lens(file, name) {
  const found = s.providers.lens.provideCodeLenses(vscode.__document(file)).find((l) => l.command.arguments[1].name === name);
  return found.command.arguments[1];
}

function dump(title, folder) {
  console.log(`--- ${title}: ${s.status.text}`);
  for (const [file, list] of s.diagnostics) {
    for (const d of list) {
      console.log(`diagnostic ${path.relative(folder, file)}:${d.range.start.line + 1} ${d.message.split("\n")[0]}`);
    }
  }
  for (const x of s.runs[s.runs.length - 1].states.filter((x) => x.state !== "started")) {
    console.log(`test ${x.state} ${x.id.split(folder).join("")} ${x.messages.join(" | ")}`);
  }
}

async function workspace() {
  const { folder, thrust } = start(path.join(here, "test", "fixtures", "cargo", "workspace"), true);
  const file = (relative) => path.join(folder, relative);
  await thrust.verify(vscode.__document(file("app/src/main.rs")));
  dump("workspace", folder);
  await thrust.verify(vscode.__document(file("arith/src/lib.rs")), lens(file("arith/src/lib.rs"), "scale"));
  dump("Pair::scale only", folder);
  await thrust.verify(vscode.__document(file("both/src/main.rs")), lens(file("both/src/main.rs"), "helper"));
  dump("helper of the binary of a package with a library", folder);
  let item;
  s.controller.items.forEach((root) => root.children.forEach((child) => (item = child.label === "sextuple" ? child : item)));
  await s.profile(new vscode.TestRunRequest([item]), token);
  dump("sextuple from the Testing view", folder);
  await s.profile(new vscode.TestRunRequest(undefined), token);
  dump("all from the Testing view", folder);
}

async function singleFile(name, fns) {
  const { folder, thrust } = start(path.join(here, "test", "fixtures", name), false);
  const file = path.join(folder, name);
  await thrust.verify(vscode.__document(file));
  dump(name, folder);
  for (const fn of fns) {
    await thrust.verify(vscode.__document(file), lens(file, fn));
    dump(`${name}: ${fn} only`, folder);
  }
}

(async () => {
  await workspace();
  await singleFile("unsafe.rs", ["main", "withdraw"]);
  await singleFile("trusted.rs", ["bad", "twin"]);
  await singleFile("nested.rs", ["outer"]);
})();
