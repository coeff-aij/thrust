// Stands in for cargo in the tests: replays a captured case of capture-cargo.sh.
// Usage: node fake-cargo.js <case directory> <the arguments the runner adds...>
// `metadata` prints the case's workspace metadata (../metadata.json); anything else empties
// THRUST_VSCODE_REPORT_DIR, as the wrapper removes the report of each crate it runs and a check
// runs every crate, copies the case's reports there and prints its messages. With FAKE_WORKSPACE set,
// /workspace is replaced by it, and with FAKE_LOG set each call appends its arguments there.
// With FAKE_HOLD set, a check waits until that file exists before it answers.
const fs = require("fs");
const path = require("path");

const [dir, ...args] = process.argv.slice(2);
const workspace = process.env.FAKE_WORKSPACE;
const read = (file) => {
  const text = fs.readFileSync(file, "utf8");
  return workspace ? text.split("/workspace").join(workspace) : text;
};
if (process.env.FAKE_LOG) {
  fs.appendFileSync(process.env.FAKE_LOG, `${args.join(" ")}\n`);
}
if (args.includes("metadata")) {
  process.stdout.write(read(path.join(dir, "..", "metadata.json")));
  return;
}
const hold = process.env.FAKE_HOLD;
const deadline = Date.now() + 10000;
while (hold && !fs.existsSync(hold) && Date.now() < deadline) {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 20);
}
const reports = path.join(dir, "reports");
const reportDir = process.env.THRUST_VSCODE_REPORT_DIR;
for (const name of fs.readdirSync(reportDir)) {
  fs.rmSync(path.join(reportDir, name));
}
for (const name of fs.existsSync(reports) ? fs.readdirSync(reports) : []) {
  fs.writeFileSync(path.join(reportDir, name), read(path.join(reports, name)));
}
process.stdout.write(read(path.join(dir, "stdout.jsonl")));
process.exitCode = Number(fs.readFileSync(path.join(dir, "exit"), "utf8"));
