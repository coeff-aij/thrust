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
    let header = format!(r#"{{"kind":"report","version":3,"root":"{root}","#);
    assert!(stdout.starts_with(&header), "{stdout}");
    let step = r#""via":"c0","obligation":"loop entry","span":{"file":"tests/report/loop_fail.rs","line":9,"column":5,"end_line":14,"end_column":6}"#;
    assert!(stdout.contains(step), "{stdout}");
    let premise = r#"{"text":"main.loop#1(x, y)","span":{"file":"tests/report/loop_fail.rs","line":9,"column":11,"end_line":9,"end_column":17}}"#;
    assert!(stdout.contains(premise), "{stdout}");
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
            r#"{"kind":"verdict","verdict":"unsat","refutations":"one per query","message":null,"functions":null}"#
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

/// A write breaking a parameter's written refinement labels that refinement.
#[test]
fn report_labels_the_refinement_a_write_breaks() {
    let output = report("refinement_write.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: refinement of `x` in `set`"),
        "{stderr}"
    );
    let label = stderr
        .lines()
        .skip_while(|l| !l.contains("#[thrust_macros::param(x: &mut { v: i64 | v >= 0 })]"))
        .nth(1)
        .unwrap_or_default();
    assert!(
        label.contains("------ the annotation it checks"),
        "{stderr}"
    );
}

/// A call to a std function without a specification stops the analysis with an error at the
/// call naming the function and how to give it a contract, not a panic.
#[test]
fn a_call_without_a_specification_is_an_error_at_the_call() {
    let output = report("no_spec.rs", "1");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert!(
        stderr.contains(
            "error: thrust: no specification of `core::num::<impl i64>::pow`, which `main` calls\n \
             --> "
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("tests/report/no_spec.rs:2:13\n"),
        "{stderr}"
    );
    assert!(stderr.contains("`#[thrust::trusted]`"), "{stderr}");
    assert_eq!(output.status.code(), Some(1), "{stderr}");
}

/// The line of the refuted constraint and that of its values.
fn refuted_lines(fixture: &str) -> (String, String) {
    let output = report(fixture, "failure");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let line = |prefix: &str| {
        let found = stderr.lines().find(|l| l.contains(prefix));
        found.unwrap_or_default().to_owned()
    };
    (line("= note: c"), line("where it fails:"))
}

/// A variable is never named for a value it no longer holds: after a loop with a written
/// invariant, a variable assigned again shows its new value, and the value it held at the loop
/// is unnamed; so is one a shadowing `let` hides and one moved out.
#[test]
fn a_name_stands_only_for_the_value_the_variable_holds() {
    let (constraint, values) = refuted_lines("name_after_reassign.rs");
    assert!(
        constraint.contains("(k >= n ∧ i = 5 ∧ k != n + 1) ==> k < 0"),
        "{constraint}"
    );
    assert!(values.contains("i = 5"), "{values}");
    let (constraint, _) = refuted_lines("name_after_shadow.rs");
    assert!(!constraint.contains(" i >= n"), "{constraint}");
    assert!(constraint.contains("__tmp_chc_"), "{constraint}");
    let (constraint, _) = refuted_lines("name_after_moved.rs");
    assert!(!constraint.contains(" b >= n"), "{constraint}");
    assert!(constraint.contains("__tmp_chc_"), "{constraint}");
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
/// equation in both, and a premise the refinements of a `&mut` repeat is shown once. In JSON an
/// unknown applied is at the code of its template, the entry block's at the signature; another
/// premise has no span.
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
        check.contains(
            r#""premises":[{"text":"check.bb0(x, old(x) ← x)","span":{"file":"tests/report/bounds.rs","line":2,"column":1,"end_line":2,"end_column":17}},{"text":"x = 0","span":null}]"#
        ),
        "{stdout}"
    );
    let identity = stdout
        .lines()
        .find(|l| l.contains(r#""kind":"failure""#) && l.contains(r#""fn":"identity""#))
        .unwrap_or_default();
    assert_eq!(
        identity.matches(r#""text":"°x >= 0""#).count(),
        1,
        "{stdout}"
    );
}

/// A constraint applies an unknown as the run shows a fact: each argument by the variable of the
/// template it is (`name ← term`, apart from the `:=` of a solution), a `&mut` as `*x` and `°x`,
/// also where its term is a variable, never as a `<current, final>` pair.
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
        swap.iter().any(|l| l.contains("swap.bb0(*x ← ")),
        "{stdout}"
    );
    assert!(swap.iter().all(|l| !l.contains('<')), "{stdout}");
    assert!(
        swap.iter().any(|l| l.contains("swap.pre(*x, °x, *y, °y)")),
        "{stdout}"
    );
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

/// A law, its proof restated as a law on the impl, and the parameters a lemma's contract reads
/// raise no lint.
#[test]
fn laws_and_lemmas_raise_no_warning() {
    let stderr = warnings_of("law_proof.rs");
    assert!(!stderr.contains("warning"), "{stderr}");
}

/// The program's own lints survive: an empty method of a trait impl and a lemma with a body
/// warn of what they leave unused.
#[test]
fn ordinary_warnings_survive() {
    let stderr = warnings_of("ordinary_warnings.rs");
    assert!(stderr.contains("unused variable: `node`"), "{stderr}");
    assert!(stderr.contains("unused variable: `unused`"), "{stderr}");
    // A parameter its contract names only as a closure's binder is not read.
    assert!(stderr.contains("unused variable: `n`"), "{stderr}");
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
    // A whole query without an answer names the functions of its clauses, as a part does.
    let verdict = r#"{"kind":"verdict","verdict":"timeout","refutations":"one per query","message":"Timeout(1s)","functions":[{"fn":"main","span":{"file":"tests/report/loop_fail.rs","line":6,"column":1,"end_line":16,"end_column":2}}]}"#;
    assert!(stdout.contains(verdict), "{stdout}");
}

/// When `z3` cannot read a query that has sequences or forall sorts, the error says that PCSat
/// can.
#[test]
fn an_unreadable_query_points_to_pcsat() {
    let stderr = warnings_of("for_range_needs_pcsat.rs");
    assert!(
        stderr.contains("help: the query has forall sorts or sequences, which `z3` does not read"),
        "{stderr}"
    );
}

/// The PCSat help is only for a query `z3` reports it cannot read, not for another failure.
#[test]
fn other_failures_get_no_pcsat_help() {
    let stderr = warnings_of("loop_fail.rs");
    assert!(stderr.contains("verification error: Unsat"), "{stderr}");
    assert!(!stderr.contains("PCSat"), "{stderr}");
    let root = env!("CARGO_MANIFEST_DIR");
    let output = Command::new(env!("CARGO_BIN_EXE_thrust-rustc"))
        .args([
            "-C",
            "debug-assertions=off",
            "tests/report/for_range_needs_pcsat.rs",
        ])
        .current_dir(root)
        .env_remove("THRUST_REPORT")
        .env_remove("THRUST_SPLIT")
        .env_remove("THRUST_SOLVER")
        .env("THRUST_SOLVER_ARGS", "-bogusflag")
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("PCSat"), "{stderr}");
}

/// A user predicate is applied as an unknown is, `p(x, y)`, not curried.
#[test]
fn a_user_predicate_is_applied_with_parentheses() {
    let output = report("predicate_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("::is_double(*old(self), °old(self))"),
        "{stderr}"
    );
}

/// A refuted loop preservation labels the `invariant!` it checks, as a loop entry does.
#[test]
fn report_labels_the_invariant_a_preservation_checks() {
    let output = report("invariant_not_preserved.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("thrust: refuted: loop preservation in `main`"),
        "{stderr}"
    );
    let label = stderr
        .lines()
        .skip_while(|l| !l.contains("thrust_macros::invariant!(|p: &mut i64| *p >= 1);"))
        .nth(1)
        .unwrap_or_default();
    assert!(label.contains("the annotation it checks"), "{stderr}");
}

/// `#[thrust_macros::law]` on an impl item must implement a law of its trait.
#[test]
fn a_restated_law_must_be_one() {
    let stderr = warnings_of("law_not_a_law.rs");
    assert!(
        stderr.contains("`#[thrust_macros::law]` on a method that implements no law of a trait"),
        "{stderr}"
    );
}

/// A run's step for a return value is at the closing brace, apart from the function's entry; the
/// error of a refuted `ensures` is at the signature.
#[test]
fn a_return_is_at_the_closing_brace() {
    let output = report("swap_half.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("return value, tests/report/swap_half.rs:3:1]"),
        "{stderr}"
    );
    assert!(
        stderr.contains("function entry, tests/report/swap_half.rs:1:1]"),
        "{stderr}"
    );
}

/// A solution defines an unknown with `:=`; an unknown's argument is given with `←`, and one of
/// no template variable as `_ ← term` unless another argument shows that term, so they read
/// apart; a 1-tuple reads `(x,)`, and a unit value is not listed where a goal fails.
#[test]
fn solutions_and_arguments_read_apart() {
    let output = report("loop_fail.rs", "constraints");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("main.loop#1(x ← "), "{stderr}");
    assert!(!stderr.contains(" := "), "{stderr}");
    let solved = report("inferred_pass.rs", "solution,constraints");
    let stderr = String::from_utf8_lossy(&solved.stderr);
    assert!(stderr.contains("double.pre(x) := "), "{stderr}");
    // An argument of no template variable is left out where another argument shows its term.
    let call = report("take_max_same.rs", "constraints");
    let stderr = String::from_utf8_lossy(&call.stderr);
    assert!(stderr.contains("main.take_max#1(*m, °m, a ← "), "{stderr}");
    assert!(!stderr.contains("_ ← a,"), "{stderr}");
}

/// The constraint of a law proved by an empty body is at the law's `ensures`, which it checks,
/// not at the empty body; and JSON places a refuted `ensures` where the error is, at the
/// signature.
#[test]
fn a_law_proof_and_a_refuted_ensures_are_where_they_are_read() {
    let output = report("law_proof.rs", "constraints");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let law = stderr
        .lines()
        .find(|l| l.contains("ensures (") && l.contains("count_nonneg"))
        .unwrap_or_default();
    assert!(
        law.contains("ensures (tests/report/law_proof.rs:10:"),
        "{stderr}"
    );
    let json = report_with(
        "ensures_fail.rs",
        "failure",
        &[("THRUST_REPORT_FORMAT", "json")],
    );
    let stdout = String::from_utf8_lossy(&json.stdout);
    let at = r#""obligation":"ensures""#;
    let failure = stdout.lines().find(|l| l.contains(at)).unwrap_or_default();
    assert!(
        failure.contains(r#""span":{"file":"tests/report/ensures_fail.rs","line":3,"column":1,"#),
        "{stdout}"
    );
}

/// A parameter read only inside a formula macro of a lemma's contract (`pre!`, `post!`) is read;
/// one only a closure's binder names is not.
#[test]
fn parameters_read_inside_formula_macros_raise_no_warning() {
    let stderr = warnings_of("macro_mentions.rs");
    for read in ["`f`", "`x`", "`y`"] {
        assert!(
            !stderr.contains(&format!("unused variable: {read}")),
            "{stderr}"
        );
    }
    assert!(stderr.contains("unused variable: `n`"), "{stderr}");
}

/// A query z3 cannot read (its forall sorts) is an error with the PCSat help, with the report as
/// without it: the error lines before z3's verdict are not taken for the failed evidence the
/// report asks for after it.
#[test]
fn an_unreadable_query_is_an_error_with_the_report_too() {
    let plain = warnings_of("law_fails_at_impl.rs");
    assert!(
        plain.contains("error: verification error: Error"),
        "{plain}"
    );
    assert!(plain.contains("which `z3` does not read"), "{plain}");
    let output = report("law_fails_at_impl.rs", "1");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error: verification error: Error"),
        "{stderr}"
    );
    assert!(stderr.contains("which `z3` does not read"), "{stderr}");
}

/// A 1-tuple reads as Rust writes it, and a unit result is not among the values.
#[test]
fn tuples_and_units_read_as_rust_writes_them() {
    let output = report("predicate_fail.rs", "failure");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let values = stderr
        .lines()
        .find(|l| l.contains("where it fails"))
        .unwrap_or_default();
    assert!(values.contains(",)") && !values.contains(", )"), "{stderr}");
    assert!(!values.contains("= ()"), "{stderr}");
}
