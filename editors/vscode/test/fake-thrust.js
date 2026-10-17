// Stands in for thrust-rustc in the runner's test: replays a captured case.
// Usage: node fake-thrust.js <case directory> <the arguments the runner adds...>
const fs = require("fs");
const path = require("path");

const dir = process.argv[2];
const report = path.join(dir, "report.jsonl");
if (fs.existsSync(report)) {
  fs.copyFileSync(report, process.env.THRUST_REPORT_FILE);
}
process.stderr.write(fs.readFileSync(path.join(dir, "stderr.jsonl")));
process.exitCode = Number(fs.readFileSync(path.join(dir, "exit"), "utf8"));
