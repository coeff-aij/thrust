use std::process::{Command, Output};

fn run(fixture: &str, split: Option<&str>) -> Output {
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
