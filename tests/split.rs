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
        .env_remove("THRUST_OUTPUT_DIR");
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
}

/// A function whose clauses a written invariant cuts into two parts: the failing part's error
/// names the lines its clauses come from, and a note says why one function is in two parts.
#[test]
fn a_function_in_two_parts_is_explained() {
    let output = run("invariant_parts.rs", Some("2"));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(stderr.contains("in part 0 of 2, of "), "{stderr}");
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
    let part = r#"{"kind":"part","id":1,"clauses":1,"functions":[{"fn":"count_to","span":{"file":"#;
    assert!(stdout.contains(part), "{stdout}");
}
