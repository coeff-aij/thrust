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
    ui_test::run_tests(config).unwrap();
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
