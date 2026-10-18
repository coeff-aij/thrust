// Stands in for thrust-rustc in the wrapper's test: writes a dep-info file where rustc would,
// and prints the arguments and Thrust's variables it was given as JSON.
const fs = require("fs");
const path = require("path");

const args = process.argv.slice(2);
const value = (name) => args[args.indexOf(name) + 1];
const extra = args.find((a) => a.startsWith("extra-filename="));
if (args.includes("--out-dir")) {
  const file = path.join(value("--out-dir"), `${value("--crate-name")}${extra ? extra.slice("extra-filename=".length) : ""}.d`);
  fs.writeFileSync(file, "deps: src/lib.rs\n");
}
const env = Object.fromEntries(Object.entries(process.env).filter(([k]) => k.startsWith("THRUST_") && !k.startsWith("THRUST_VSCODE_")));
// The variables of the wrapper's test named as the wrapper's own shell variables would be.
const kept = Object.fromEntries(["name", "crate", "status", "report", "sep"].filter((k) => k in process.env).map((k) => [k, process.env[k]]));
process.stdout.write(JSON.stringify({ args, env, kept }));
