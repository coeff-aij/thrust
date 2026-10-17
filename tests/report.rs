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
        .env_remove("THRUST_SPLIT")
        .env_remove("THRUST_CACHE_DIR")
        .env_remove("THRUST_REPORT_FORMAT")
        .env_remove("THRUST_REPORT_FILE")
        .env_remove("THRUST_REPORT_ONLY")
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
        stderr.contains("(x = 1 ∧ y = 1) ==> main.loop#1(x, y)"),
        "{stderr}"
    );
    assert!(stderr.contains("main.loop#1(x = 1, y = 1)"), "{stderr}");
    assert!(stderr.contains("main.rand#1(rand#1, x, y)"), "{stderr}");
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
            "it assumes the written contract of `natural` (tests/report/written_call.rs:2:26)"
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
    let header = format!(r#"{{"kind":"report","version":2,"root":"{root}","#);
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
        stdout.contains(
            r#"{"kind":"verdict","verdict":"unsat","refutations":"one per query","message":null}"#
        ),
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

/// The warnings of compiling `fixture` with its lints on, without the report.
fn warnings_of(fixture: &str) -> String {
    let root = env!("CARGO_MANIFEST_DIR");
    let output = Command::new(env!("CARGO_BIN_EXE_thrust-rustc"))
        .args(["-C", "debug-assertions=off"])
        .arg(format!("tests/report/{fixture}"))
        .current_dir(root)
        .env_remove("THRUST_REPORT")
        .env_remove("THRUST_SPLIT")
        .env_remove("THRUST_SOLVER")
        .env_remove("THRUST_OUTPUT_DIR")
        .output()
        .unwrap();
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// The lints of the program are its own: none come from the injected `std.rs`.
#[test]
fn no_warning_comes_from_the_injected_std() {
    let stderr = warnings_of("unused_local.rs");
    assert!(stderr.contains("unused variable: `unused`"), "{stderr}");
    assert!(!stderr.contains("thrust std injected"), "{stderr}");
}

/// With the report, the refutation is the verification error, at the obligation, so an editor
/// that drops a diagnostic without a span shows it, and it is the one error; in JSON, the error
/// is at that obligation.
#[test]
fn the_verification_error_is_the_refutation() {
    let output = report("loop_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let error = stderr
        .split("error: verification error: Unsat (thrust: refuted: assertion in `main`)\n  --> ")
        .nth(1)
        .unwrap_or_default();
    assert!(error.contains("loop_fail.rs:15:5\n"), "{stderr}");
    assert!(
        stderr.contains("aborting due to 1 previous error"),
        "{stderr}"
    );
    let json = report_with(
        "loop_fail.rs",
        "failure",
        &[("THRUST_REPORT_FORMAT", "json")],
    );
    let stderr = String::from_utf8_lossy(&json.stderr);
    let error = stderr
        .split("error: verification error: Unsat\n  --> ")
        .nth(1)
        .unwrap_or_default();
    assert!(error.contains("loop_fail.rs:15:5\n"), "{stderr}");
}

/// Each clause of a `closure!` contract is labelled by its formula, and so is a specification
/// attribute's; JSON gives the spans as the failure's `annotation`.
#[test]
fn report_labels_each_clause_by_its_formula() {
    let output = report("closure_two_clauses.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let labelled = |clause: &str| {
        let mut lines = stderr.lines().skip_while(|l| !l.contains(clause));
        lines
            .nth(1)
            .unwrap_or_default()
            .contains("a clause of the annotation it checks")
    };
    assert!(labelled("ensures(result >= x)"), "{stderr}");
    assert!(labelled("ensures(result == x + 2)"), "{stderr}");
    let json = report_with(
        "ensures_fail.rs",
        "failure",
        &[("THRUST_REPORT_FORMAT", "json")],
    );
    let stdout = String::from_utf8_lossy(&json.stdout);
    let annotation = r#""annotation":[{"file":"tests/report/ensures_fail.rs","line":2,"column":26,"end_line":2,"end_column":36}]"#;
    assert!(stdout.contains(annotation), "{stdout}");
}

/// A run through a call to a function of the injected `std.rs` names no written contract of the
/// program's.
#[test]
fn report_names_no_contract_of_the_injected_std() {
    let output = report("std_replace.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("after call to `std::mem::replace`"),
        "{stderr}"
    );
    assert!(!stderr.contains("it assumes"), "{stderr}");
}

/// The premises of a constraint are those its formula shows: two bounds by one value are one
/// equation in both, and a premise the refinements of a `&mut` repeat is shown once.
#[test]
fn premises_are_the_formula_s_and_each_is_once() {
    let output = report_with(
        "bounds.rs",
        "failure,constraints",
        &[("THRUST_REPORT_FORMAT", "json")],
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let check = stdout
        .lines()
        .find(|l| l.contains(r#""fn":"check""#) && l.contains("assertion"))
        .unwrap_or_default();
    assert!(
        check.contains(r#""premises":["check.bb0(x, old(x) = x)","x = 0"]"#),
        "{stdout}"
    );
    let identity = stdout
        .lines()
        .find(|l| l.contains(r#""kind":"failure""#) && l.contains(r#""fn":"identity""#))
        .unwrap_or_default();
    assert_eq!(identity.matches(r#""°x >= 0""#).count(), 1, "{stdout}");
}

/// A constraint applies an unknown as the run shows a fact: each argument by the variable of the
/// template it is, a `&mut` as `*x` and `°x`, never as a `<current, final>` pair.
#[test]
fn constraints_name_the_arguments_of_an_unknown() {
    let output = report_with(
        "swap_half.rs",
        "constraints",
        &[("THRUST_REPORT_FORMAT", "json")],
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let swap: Vec<&str> = stdout
        .lines()
        .filter(|l| l.contains(r#""fn":"swap""#))
        .collect();
    assert!(
        swap.iter().any(|l| l.contains("swap.bb0(*x = ")),
        "{stdout}"
    );
    assert!(swap.iter().all(|l| !l.contains('<')), "{stdout}");
}

/// A refuted loop entry or preservation labels the `invariant!` it checks.
#[test]
fn report_labels_the_invariant_a_loop_checks() {
    let output = report("invariant_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: loop entry in `count_to`"),
        "{stderr}"
    );
    let label = stderr
        .lines()
        .skip_while(|l| !l.contains("thrust_macros::invariant!(|i: i64| i >= 1);"))
        .nth(1)
        .unwrap_or_default();
    assert!(label.contains("the annotation it checks"), "{stderr}");
}

/// A law, its proof by an empty body and a lemma raise no lint: they are not called and need not
/// read their parameters.
#[test]
fn laws_and_their_proofs_raise_no_warning() {
    let stderr = warnings_of("law_proof.rs");
    assert!(!stderr.contains("warning"), "{stderr}");
}

/// The JSON header states how columns count as values, each step of a run gives its unknown and
/// arguments apart from the fact's text, and a verdict that is no answer says what it was.
#[test]
fn json_states_columns_facts_and_the_solver_s_limit() {
    let json = report_with("loop_fail.rs", "1", &[("THRUST_REPORT_FORMAT", "json")]);
    let stdout = String::from_utf8_lossy(&json.stdout);
    assert!(
        stdout.contains(r#""columns":{"base":1,"unit":"char","end":"exclusive"}"#),
        "{stdout}"
    );
    let step = r#""pred":"main.loop#1","args":[{"name":"x","value":"1"},{"name":"y","value":"1"}]"#;
    assert!(stdout.contains(step), "{stdout}");

    use std::os::unix::fs::PermissionsExt as _;
    let dir = std::env::temp_dir().join(format!("thrust-slow-solver-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("slow");
    std::fs::write(&solver, "#!/bin/sh\nsleep 5\necho sat\n").unwrap();
    std::fs::set_permissions(&solver, std::fs::Permissions::from_mode(0o755)).unwrap();
    let slow = report_with(
        "loop_fail.rs",
        "1",
        &[
            ("THRUST_REPORT_FORMAT", "json"),
            ("THRUST_SOLVER", solver.to_str().unwrap()),
            ("THRUST_SOLVER_TIMEOUT_SECS", "1"),
        ],
    );
    std::fs::remove_dir_all(&dir).unwrap();
    let stdout = String::from_utf8_lossy(&slow.stdout);
    let verdict = r#"{"kind":"verdict","verdict":"timeout","refutations":"one per query","message":"Timeout(1s)"}"#;
    assert!(stdout.contains(verdict), "{stdout}");
}
