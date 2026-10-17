use std::process::{Command, Output};

fn report(fixture: &str, items: &str) -> Output {
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/report")
        .join(fixture);
    Command::new(env!("CARGO_BIN_EXE_thrust-rustc"))
        .args(["-Awarnings", "-C", "debug-assertions=off"])
        .arg(fixture)
        .env("THRUST_REPORT", items)
        .env_remove("THRUST_SOLVER")
        .env_remove("THRUST_OUTPUT_DIR")
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
    assert!(stderr.contains("main.loop#1(x: Int, y: Int)"), "{stderr}");
    assert!(
        stderr.contains("thrust: refuted: assertion in `main`"),
        "{stderr}"
    );
    assert!(stderr.contains("==> y >= 2"), "{stderr}");
    assert!(
        stderr.contains("x == 1 && y == 1 ==> main.loop#1(x, y)"),
        "{stderr}"
    );
    assert!(stderr.contains("main.loop#1(x = 1, y = 1)"), "{stderr}");
    assert!(
        stderr.contains("main.rand#1(__tmp_mir_main_3;; x, y)"),
        "{stderr}"
    );
}
