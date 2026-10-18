use std::process::{Command, Output};

fn cargo_check(fixture: &str, envs: &[(&str, &str)]) -> Output {
    let target_dir = tempfile::tempdir().unwrap();
    cargo_check_in(fixture, target_dir.path(), &[], envs)
}

/// `cargo check` of `fixture` into `target_dir`, with `args`.
fn cargo_check_in(
    fixture: &str,
    target_dir: &std::path::Path,
    args: &[&str],
    envs: &[(&str, &str)],
) -> Output {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/cargo")
        .join(fixture);
    Command::new(env!("CARGO"))
        .args(["check", "--offline", "--locked"])
        .args(args)
        .arg("--manifest-path")
        .arg(fixture.join("Cargo.toml"))
        .env("RUSTC", env!("CARGO_BIN_EXE_thrust-rustc"))
        .env("RUSTFLAGS", "-C debug-assertions=false")
        .env("CARGO_TARGET_DIR", target_dir)
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("THRUST_OUTPUT_DIR")
        .envs(envs.iter().copied())
        .output()
        .unwrap()
}

#[test]
fn cargo_check_passes_verification() {
    let output = cargo_check("pass", &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn cargo_check_reports_verification_failure() {
    let output = cargo_check("fail", &[]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{stderr}");
    assert!(stderr.contains("verification error: Unsat"), "{stderr}");
}

#[test]
fn cargo_check_trusts_contracts_outside_verify_only() {
    let output = cargo_check("verify_only", &[("THRUST_VERIFY_ONLY", "g")]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// `cargo check` of `workspace` into `target_dir`, with cargo's messages as JSON.
fn check_workspace(target_dir: &std::path::Path, envs: &[(&str, &str)]) -> Output {
    let args = ["--workspace", "--message-format=json"];
    cargo_check_in("workspace", target_dir, &args, envs)
}

/// Whether cargo found each crate it checked fresh, from its messages.
fn fresh(output: &Output) -> Vec<bool> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| line.contains(r#""reason":"compiler-artifact""#))
        .map(|line| line.contains(r#""fresh":true"#))
        .collect()
}

/// A crate that verifies writes its metadata, so a crate of the workspace using it compiles, and
/// cargo finds both fresh when nothing changed; a variable Thrust reads changing checks them
/// again.
#[test]
fn cargo_check_keeps_verified_crates_fresh() {
    let target_dir = tempfile::tempdir().unwrap();
    let first = check_workspace(target_dir.path(), &[]);
    let stderr = String::from_utf8_lossy(&first.stdout);
    assert!(first.status.success(), "{stderr}");
    assert_eq!(fresh(&first), [false, false], "{stderr}");

    let second = check_workspace(target_dir.path(), &[]);
    let stderr = String::from_utf8_lossy(&second.stdout);
    assert!(second.status.success(), "{stderr}");
    assert_eq!(fresh(&second), [true, true], "{stderr}");

    let changed = check_workspace(target_dir.path(), &[("THRUST_SOLVER_TIMEOUT_SECS", "31")]);
    let stderr = String::from_utf8_lossy(&changed.stdout);
    assert!(changed.status.success(), "{stderr}");
    assert_eq!(fresh(&changed), [false, false], "{stderr}");
}
