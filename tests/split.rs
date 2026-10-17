use std::process::{Command, Output};

fn run(fixture: &str, split: Option<&str>) -> Output {
    run_with(fixture, split, &[])
}

fn run_with(fixture: &str, split: Option<&str>, env: &[(&str, &str)]) -> Output {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/split")
        .join(fixture);
    let mut command = Command::new(env!("CARGO_BIN_EXE_thrust-rustc"));
    command
        .args(["-Awarnings", "-C", "debug-assertions=off"])
        .arg(fixture)
        .env_remove("THRUST_SOLVER")
        .env_remove("THRUST_CACHE_DIR")
        .env_remove("THRUST_OUTPUT_DIR")
        .env_remove("THRUST_PRETTY_OUTPUT")
        .env_remove("THRUST_REPORT")
        .env_remove("THRUST_REPORT_FORMAT")
        .env_remove("THRUST_REPORT_FILE")
        .env_remove("THRUST_REPORT_ONLY");
    match split {
        Some(jobs) => command.env("THRUST_SPLIT", jobs),
        None => command.env_remove("THRUST_SPLIT"),
    };
    command.envs(env.iter().copied());
    command.output().unwrap()
}

/// Two functions with written contracts are solved apart, and the one whose ensures fails is
/// reported with its part; the verdict is the one the whole query gets.
#[test]
fn a_failing_part_names_its_function() {
    let whole = run("two_parts.rs", None);
    let parts = run("two_parts.rs", Some("2"));
    let stderr = String::from_utf8_lossy(&parts.stderr);
    assert!(!whole.status.success());
    assert!(!parts.status.success(), "{stderr}");
    assert!(stderr.contains("`bad`"), "{stderr}");
    assert!(!stderr.contains("`good`"), "{stderr}");
    assert!(stderr.contains("parts solved on their own"), "{stderr}");
}

#[test]
fn a_split_that_is_no_number_is_an_error() {
    let output = run("two_parts.rs", Some("many"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("`THRUST_SPLIT`: `many` is no number of parts"),
        "{stderr}"
    );
}

/// The report of a split run shows the failure of the refuted part, with the values where it
/// fails.
#[test]
fn a_split_run_reports_the_refuted_part() {
    let output = run_with("two_parts.rs", Some("2"), &[("THRUST_REPORT", "1")]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: ensures in `bad`"),
        "{stderr}"
    );
    assert!(stderr.contains("where it fails: x = 0"), "{stderr}");
    assert!(
        stderr.contains(
            "error: verification error: Unsat (thrust: refuted: ensures in `bad`)\n  --> "
        ),
        "{stderr}"
    );
}

/// A function whose clauses a written invariant cuts into two parts: the failing part's error
/// names the lines its clauses come from, and a note says why one function is in two parts.
#[test]
fn a_function_in_two_parts_is_explained() {
    let output = run("invariant_parts.rs", Some("2"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    // Parts are numbered from 1.
    assert!(stderr.contains("in part 1 of 2, of "), "{stderr}");
    assert!(
        stderr.contains("invariant_parts.rs:1-8), `main` ("),
        "{stderr}"
    );
    assert!(
        stderr.contains("a function can be in several parts: `count_to` in 2"),
        "{stderr}"
    );
}

/// A split run shows the contracts inferred in the parts that are solved, beside the failure of
/// the part that is refuted.
#[test]
fn a_split_run_shows_what_the_solved_parts_infer() {
    let output = run_with("inferred_parts.rs", Some("2"), &[("THRUST_REPORT", "1")]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: ensures in `bad`"),
        "{stderr}"
    );
    assert!(
        stderr.contains("inferred: fn double(x: {int | x = 2})"),
        "{stderr}"
    );
}

/// A part line of the JSON report names each function with the span of its clauses.
#[test]
fn a_part_line_spans_its_functions() {
    let output = run_with(
        "invariant_parts.rs",
        Some("2"),
        &[("THRUST_REPORT", "1"), ("THRUST_REPORT_FORMAT", "json")],
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let part = r#"{"kind":"part","id":2,"clauses":1,"functions":[{"fn":"count_to","span":{"file":"#;
    assert!(stdout.contains(part), "{stdout}");
}

/// A part's model is read over the sorts its own query declares, which it numbers apart from
/// the other parts (here the tuple of a `&mut` and an integer of `gcd`'s loop).
#[test]
fn a_part_model_is_read_over_its_own_sorts() {
    let output = run_with("tuple_sort_part.rs", Some("2"), &[("THRUST_REPORT", "1")]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(stderr.contains("inferred: fn gcd("), "{stderr}");
}

/// The report's second runs of the parts write no file: `THRUST_OUTPUT_DIR` gets each part's
/// query once, and neither the whole query nor `THRUST_PRETTY_OUTPUT` is written.
#[test]
fn the_report_of_a_split_run_writes_only_the_parts() {
    let dir = std::env::temp_dir().join(format!("thrust-split-output-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let pretty = dir.join("pretty.txt");
    let output = run_with(
        "two_parts.rs",
        Some("2"),
        &[
            ("THRUST_REPORT", "1"),
            ("THRUST_OUTPUT_DIR", dir.to_str().unwrap()),
            ("THRUST_PRETTY_OUTPUT", pretty.to_str().unwrap()),
        ],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let files: Vec<String> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(
        files.iter().any(|f| f == "thrust_output_part0.smt2"),
        "{files:?} {stderr}"
    );
    assert!(
        !files.iter().any(|f| f == "thrust_output.smt2"),
        "{files:?}"
    );
    assert!(!files.iter().any(|f| f == "pretty.txt"), "{files:?}");
}

/// A `z3` on `PATH` that answers `unknown` when asked for a model or a refutation, so that only
/// the report's second runs fail.
fn z3_without_evidence() -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt as _;
    let dir = std::env::temp_dir().join(format!("thrust-z3-no-evidence-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let z3 = dir.join("z3");
    let script = "#!/bin/sh\n\
        file=\"\"; for a in \"$@\"; do file=\"$a\"; done\n\
        if grep -q 'get-model\\|get-proof' \"$file\"; then echo unknown; exit 0; fi\n\
        PATH=\"${PATH#*:}\" exec z3 \"$@\"\n";
    std::fs::write(&z3, script).unwrap();
    std::fs::set_permissions(&z3, std::fs::Permissions::from_mode(0o755)).unwrap();
    dir
}

/// When the second run of a part gives no refutation or no model, the report says so, with what
/// it gave, rather than nothing or that the part has no solution.
#[test]
fn a_failed_second_run_is_reported_with_its_verdict() {
    let dir = z3_without_evidence();
    let path = format!("{}:{}", dir.display(), std::env::var("PATH").unwrap());
    let output = run_with(
        "inferred_parts.rs",
        Some("2"),
        &[("THRUST_REPORT", "1,template"), ("PATH", &path)],
    );
    std::fs::remove_dir_all(&dir).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "thrust: no failing obligation to show for part 1: the second run, asked for a \
             refutation, gave none (unknown)"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("no solution: the second run, asked for a model, gave none (unknown)"),
        "{stderr}"
    );
}

/// A solver that gives no model or refutation (any but `z3`) is not asked again by the report:
/// each part is solved once.
#[test]
fn a_solver_without_evidence_solves_each_part_once() {
    use std::os::unix::fs::PermissionsExt as _;
    let dir = std::env::temp_dir().join(format!("thrust-sat-solver-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("always-sat");
    let log = dir.join("runs");
    let script = format!("#!/bin/sh\necho run >> '{}'\necho sat\n", log.display());
    std::fs::write(&solver, script).unwrap();
    std::fs::set_permissions(&solver, std::fs::Permissions::from_mode(0o755)).unwrap();
    let output = run_with(
        "two_parts.rs",
        Some("2"),
        &[
            ("THRUST_REPORT", "1"),
            ("THRUST_SOLVER", solver.to_str().unwrap()),
        ],
    );
    let runs = std::fs::read_to_string(&log)
        .unwrap_or_default()
        .lines()
        .count();
    std::fs::remove_dir_all(&dir).unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: 3 parts solved on their own"),
        "{stderr}"
    );
    assert_eq!(runs, 3, "{stderr}");
}

/// A split run's JSON states one refutation per part, and each failure names its part; without
/// the report, a failing part's error is at the code of the part.
#[test]
fn a_split_failure_names_its_part() {
    let json = run_with(
        "two_parts.rs",
        Some("2"),
        &[("THRUST_REPORT", "1"), ("THRUST_REPORT_FORMAT", "json")],
    );
    let stdout = String::from_utf8_lossy(&json.stdout);
    let verdict = r#"{"kind":"verdict","verdict":"unsat","refutations":"one per part"}"#;
    assert!(stdout.contains(verdict), "{stdout}");
    assert!(
        stdout.contains(r#"{"kind":"failure","part":2,"constraint":"#),
        "{stdout}"
    );
    let plain = run("two_parts.rs", Some("2"));
    let stderr = String::from_utf8_lossy(&plain.stderr);
    let error = stderr
        .split("error: verification error: Unsat\n  --> ")
        .nth(1)
        .unwrap_or_default();
    assert!(error.contains("two_parts.rs:9:1\n"), "{stderr}");
}

/// What needs no answer of the solver, the templates and the constraints, is shown of every part
/// as without `THRUST_SPLIT`.
#[test]
fn a_split_run_shows_the_constraints_of_every_part() {
    let notes = |split| {
        let output = run_with(
            "inferred_parts.rs",
            split,
            &[("THRUST_REPORT", "template,constraints")],
        );
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        (stderr.matches("constraints from this code").count(), stderr)
    };
    let (whole, _) = notes(None);
    let (parts, stderr) = notes(Some("2"));
    assert!(whole >= 3, "{stderr}");
    assert_eq!(parts, whole, "{stderr}");
    assert!(stderr.contains("template: fn double("), "{stderr}");
}

/// A failing part of several functions without a refutation has its error at the first and
/// labels the others.
#[test]
fn a_part_of_several_functions_spans_each() {
    let output = run("several_functions.rs", Some("2"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("`main` is in this part too"), "{stderr}");
}
