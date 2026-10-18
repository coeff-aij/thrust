// Stands in for cargo in the cargo runner's test: replays a captured case of capture-cargo.sh.
// Usage: node fake-cargo.js <case directory> <the arguments the runner adds...>
const fs = require("fs");
const path = require("path");

const dir = process.argv[2];
const reports = path.join(dir, "reports");
for (const name of fs.readdirSync(reports)) {
  fs.copyFileSync(path.join(reports, name), path.join(process.env.THRUST_VSCODE_REPORT_DIR, name));
}
process.stdout.write(fs.readFileSync(path.join(dir, "stdout.jsonl")));
process.exitCode = Number(fs.readFileSync(path.join(dir, "exit"), "utf8"));
