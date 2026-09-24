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
    ui_test::run_tests(config).unwrap();
}
