use std::path::{Path, PathBuf};

/// The wrappers that run a CoAR solver (PCSat, Spacer) in Docker.
const COAR_WRAPPERS: [&str; 2] = ["tests/thrust-pcsat-wrapper", "tests/thrust-spacer-wrapper"];

fn main() {
    let mut config = ui_test::Config::rustc("tests/ui/");
    config.program.program = env!("CARGO_BIN_EXE_thrust-rustc").into();
    config.output_conflict_handling = ui_test::ignore_output_conflict;
    // One test per core starts one solver container per core; with the wrapper's two CPUs per
    // container that oversubscribes the machine and starves PCSat's wall-clock budgets. Eight
    // at a time keeps a sweep's verdicts equal to a single run's; THRUST_UI_THREADS overrides.
    let threads = std::env::var("THRUST_UI_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8);
    config.threads = std::num::NonZeroUsize::new(threads);
    // THRUST_UI_SKIP_COAR=1 runs only the tests Z3 decides, for a machine without the CoAR image
    // (CI); the others count as filtered out.
    if std::env::var("THRUST_UI_SKIP_COAR").is_ok_and(|v| v == "1") {
        let skipped = coar_tests(Path::new("tests/ui"));
        println!(
            "THRUST_UI_SKIP_COAR=1: skipping the {} tests that name a CoAR wrapper",
            skipped.len()
        );
        config
            .skip_files
            .extend(skipped.iter().map(|path| path.display().to_string()));
    }
    // THRUST_UI_CACHE_DIR=<dir> keeps the sat/unsat verdicts of the tests in <dir>, so that a
    // development run solves only the queries that changed (see the README).
    if let Some(dir) = std::env::var_os("THRUST_UI_CACHE_DIR") {
        let skip_coar = std::env::var("THRUST_UI_SKIP_COAR").is_ok_and(|v| v == "1");
        let salt = verdict_cache_salt(skip_coar);
        config
            .program
            .envs
            .push(("THRUST_CACHE_DIR".into(), Some(dir)));
        config
            .program
            .envs
            .push(("THRUST_CACHE_SALT".into(), Some(salt.into())));
    }
    ui_test::run_tests(config).unwrap();
}

/// What decides a verdict besides the query and the solver command that Thrust's cache already
/// keys on: the CoAR image's content (not its tag, which moves), the solver configuration, and
/// the Z3 version.
fn verdict_cache_salt(skip_coar: bool) -> String {
    let z3 = command_output("z3", &["--version"]);
    if skip_coar {
        return format!("z3: {z3}");
    }
    let image = std::env::var("COAR_IMAGE").unwrap_or_else(|_| "coar:latest".into());
    let image_id = command_output(
        "docker",
        &["image", "inspect", "--format", "{{.Id}}", &image],
    );
    let config = std::env::var("COAR_CONFIG").unwrap_or_default();
    let config_dir = std::env::var_os("COAR_CONFIG_DIR")
        .map(|dir| directory_hash(Path::new(&dir)))
        .unwrap_or_default();
    format!("z3: {z3}; image: {image_id}; config: {config}; config dir: {config_dir}")
}

/// The trimmed standard output of `program`, which must succeed: the cache must not run with a
/// salt that is weaker than it claims.
fn command_output(program: &str, args: &[&str]) -> String {
    let output = std::process::Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("THRUST_UI_CACHE_DIR: cannot run `{program}`: {e}"));
    assert!(
        output.status.success(),
        "THRUST_UI_CACHE_DIR: `{program} {}` failed: {}",
        args.join(" "),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap().trim().to_string()
}

/// A hash of the names and contents of the files under `dir`.
fn directory_hash(dir: &Path) -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("THRUST_UI_CACHE_DIR: cannot read {}: {e}", dir.display()))
        .map(|entry| entry.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        path.hash(&mut hasher);
        if path.is_dir() {
            directory_hash(&path).hash(&mut hasher);
        } else {
            std::fs::read(&path).unwrap().hash(&mut hasher);
        }
    }
    format!("{:016x}", hasher.finish())
}

/// The test files under `dir` whose header sets `THRUST_SOLVER` to a CoAR wrapper.
fn coar_tests(dir: &Path) -> Vec<PathBuf> {
    let mut tests = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            tests.extend(coar_tests(&path));
        } else if path.extension().is_some_and(|ext| ext == "rs") && names_coar_wrapper(&path) {
            tests.push(path);
        }
    }
    tests
}

fn names_coar_wrapper(path: &Path) -> bool {
    let source = std::fs::read_to_string(path).unwrap();
    source
        .lines()
        .filter(|line| line.starts_with("//@rustc-env:"))
        .any(|line| COAR_WRAPPERS.iter().any(|wrapper| line.contains(wrapper)))
}
