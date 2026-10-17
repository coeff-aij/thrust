use std::process::{Command, Output};

fn report(fixture: &str, items: &str) -> Output {
    report_with(fixture, items, &[])
}

fn report_with(fixture: &str, items: &str, env: &[(&str, &str)]) -> Output {
    let root = env!("CARGO_MANIFEST_DIR");
    let fixture = std::path::Path::new(root)
        .join("tests/report")
        .join(fixture);
    Command::new(env!("CARGO_BIN_EXE_thrust-rustc"))
        .args(["-Awarnings", "-C", "debug-assertions=off"])
        .arg(fixture)
        .current_dir(root)
        .env("THRUST_REPORT", items)
        .env_remove("THRUST_SOLVER")
        .env_remove("THRUST_OUTPUT_DIR")
        .env_remove("THRUST_REPORT_FORMAT")
        .envs(env.iter().copied())
        .output()
        .unwrap()
}

/// The variables keep their names through the order a loop's unknown takes its arguments in, in
/// the constraints, the refuted goal and the run reaching it.
#[test]
fn report_names_the_variables_of_a_refuted_assertion() {
    let output = report("loop_fail.rs", "template,constraints,failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(stderr.contains("main.loop#1(x: int, y: int)"), "{stderr}");
    assert!(
        stderr.contains("thrust: refuted: assertion in `main`"),
        "{stderr}"
    );
    assert!(stderr.contains("==> y >= 2"), "{stderr}");
    assert!(
        stderr.contains("(x = 1 ∧ y = 1) ==> main.loop#1 x y"),
        "{stderr}"
    );
    assert!(stderr.contains("main.loop#1(x = 1, y = 1)"), "{stderr}");
    assert!(stderr.contains("main.rand#1 rand#1 x y"), "{stderr}");
}

/// A refuted `ensures` is shown at the end of the body, where it fails, with the annotation it
/// checks labelled; JSON names the annotation's span.
#[test]
fn report_points_at_the_refuted_annotation() {
    let output = report("ensures_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: ensures in `next`"),
        "{stderr}"
    );
    assert!(
        stderr.contains("#[thrust_macros::ensures(result > x)]"),
        "{stderr}"
    );
    assert!(stderr.contains("the annotation it checks"), "{stderr}");
}

/// A failure whose run assumes a written contract at a call names that contract.
#[test]
fn report_names_the_written_contract_a_run_assumes() {
    let output = report("written_call.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(
            "it assumes the written contract of `natural` (tests/report/written_call.rs:2:1)"
        ),
        "{stderr}"
    );
}

/// `THRUST_REPORT=1` writes to a program what it shows a person: the failure, each step of its
/// run with the obligation and the span deriving it, spans relative to the working directory, and
/// no template or constraint without a solution.
#[test]
fn json_report_shows_the_failure_alone() {
    let output = report_with("loop_fail.rs", "1", &[("THRUST_REPORT_FORMAT", "json")]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let kinds: Vec<&str> = stdout.lines().filter_map(|l| l.split('"').nth(3)).collect();
    assert_eq!(kinds, ["verdict", "failure"], "{stdout}");
    assert!(
        stdout.contains(
            r#""via":"c0","obligation":"loop entry","span":"tests/report/loop_fail.rs:9:5""#
        ),
        "{stdout}"
    );
}

/// The JSON report opens with the crate's verdict, and a failure of the whole query says that
/// the solver refutes one obligation of it.
#[test]
fn report_states_the_verdict_and_one_refutation_per_query() {
    let json = report_with("loop_fail.rs", "1", &[("THRUST_REPORT_FORMAT", "json")]);
    let stdout = String::from_utf8_lossy(&json.stdout);
    assert!(
        stdout.starts_with(r#"{"kind":"verdict","verdict":"unsat","refutations":"one per query"}"#),
        "{stdout}"
    );
    let human = report("loop_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&human.stderr);
    assert!(
        stderr.contains("the solver refutes one obligation of a query: others may fail too"),
        "{stderr}"
    );
}
