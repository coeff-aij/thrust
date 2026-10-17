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

/// `THRUST_REPORT=1` writes to a program what it shows a person: after the header and the
/// verdict, the failure, each step of its run with the obligation and the span deriving it, spans
/// as ranges relative to the root the header names, and no template or constraint without a
/// solution.
#[test]
fn json_report_shows_the_failure_alone() {
    let output = report_with("loop_fail.rs", "1", &[("THRUST_REPORT_FORMAT", "json")]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let kinds: Vec<&str> = stdout.lines().filter_map(|l| l.split('"').nth(3)).collect();
    assert_eq!(kinds, ["report", "verdict", "failure"], "{stdout}");
    let root = env!("CARGO_MANIFEST_DIR");
    let header = format!(r#"{{"kind":"report","version":1,"root":"{root}","#);
    assert!(stdout.starts_with(&header), "{stdout}");
    let step = r#""via":"c0","obligation":"loop entry","span":{"file":"tests/report/loop_fail.rs","line":9,"column":5,"end_line":14,"end_column":6}"#;
    assert!(stdout.contains(step), "{stdout}");
    // `rand`'s `ensures(true)` assumes nothing.
    assert!(stdout.contains(r#""assumes":[]"#), "{stdout}");
}

/// The JSON report states the crate's verdict, and a failure of the whole query says that
/// the solver refutes one obligation of it.
#[test]
fn report_states_the_verdict_and_one_refutation_per_query() {
    let json = report_with("loop_fail.rs", "1", &[("THRUST_REPORT_FORMAT", "json")]);
    let stdout = String::from_utf8_lossy(&json.stdout);
    assert!(
        stdout.contains(r#"{"kind":"verdict","verdict":"unsat","refutations":"one per query"}"#),
        "{stdout}"
    );
    let human = report("loop_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&human.stderr);
    assert!(
        stderr.contains("the solver refutes one obligation of a query: others may fail too"),
        "{stderr}"
    );
}

/// A refuted precondition labels the `requires` it checks, not the `ensures` written after it,
/// and a goal over no unknown is shown without a run.
#[test]
fn report_labels_the_requires_a_call_breaks() {
    let output = report("requires_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: precondition of `withdraw` in `main`"),
        "{stderr}"
    );
    let label = stderr
        .lines()
        .skip_while(|l| !l.contains("#[thrust_macros::requires(amount <= balance)]"))
        .nth(1)
        .unwrap_or_default();
    assert!(label.contains("the annotation it checks"), "{stderr}");
    assert!(!stderr.contains("how the solver reaches it"), "{stderr}");
}

/// A refuted `assert!(a != b)` reads as its condition, not as the boolean term the MIR compares
/// with `false`.
#[test]
fn report_reads_a_boolean_condition_as_a_formula() {
    let output = report("take_max_same.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("==> a != b\n"), "{stderr}");
}

/// The run shows a `&mut` by its current and final values, `*x` and `°x`, and leaves out the
/// arguments the program does not name.
#[test]
fn report_shows_a_mutable_reference_by_its_two_values() {
    let output = report("swap_half.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("swap.post(*x = 1, °x = 3, *y = 3, °y = 3)"),
        "{stderr}"
    );
    assert!(!stderr.contains("= <"), "{stderr}");
}

/// The lints of the program are its own: none come from the injected `std.rs`.
#[test]
fn no_warning_comes_from_the_injected_std() {
    let root = env!("CARGO_MANIFEST_DIR");
    let output = Command::new(env!("CARGO_BIN_EXE_thrust-rustc"))
        .args(["-C", "debug-assertions=off", "tests/report/unused_local.rs"])
        .current_dir(root)
        .env_remove("THRUST_REPORT")
        .env_remove("THRUST_SOLVER")
        .env_remove("THRUST_OUTPUT_DIR")
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("unused variable: `unused`"), "{stderr}");
    assert!(!stderr.contains("thrust std injected"), "{stderr}");
}

/// With the report, the verification error is at the obligation the report shows refuted, so an
/// editor that drops a diagnostic without a span shows it.
#[test]
fn the_verification_error_is_at_the_refuted_obligation() {
    let output = report("loop_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let error = stderr
        .split("error: verification error: Unsat\n  --> ")
        .nth(1)
        .unwrap_or_default();
    assert!(error.contains("loop_fail.rs:15:5\n"), "{stderr}");
}
