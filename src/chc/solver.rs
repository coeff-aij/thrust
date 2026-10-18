//! A generic interface for running external command-line CHC solvers.
//!
//! This module provides the [`Config`] struct for configuring and running an external
//! CHC solver. It supports setting the solver command, arguments, and timeout, and can
//! be configured through environment variables.

use super::sexp::Sexp;

/// An error that can occur when solving a [`crate::chc::System`].
#[derive(Debug, thiserror::Error)]
pub enum CheckSatError {
    #[error("unsat")]
    Unsat,
    #[error("solver error: stdout: {stdout} stderr: {stderr}")]
    Error { stdout: String, stderr: String },
    #[error("unknown output: {stdout}")]
    Unknown { stdout: String },
    /// The solver answered `sat`, but only after rejecting one or more lines
    /// of the query as unsupported (a solver that does not implement one of
    /// `declare-forall-sort`/`declare-forall-fun`/`declare-dep-exists-fun`
    /// answers `unsupported` for it and carries on). A rejected line can be
    /// an assertion the query needed, so a `sat` reached this way is not
    /// trusted: see [`read_verdict`] for why `sat` and `unsat` are not
    /// symmetric here.
    #[error(
        "solver reported sat, but not before rejecting part of the query as unsupported \
         (rejected: {rejected:?}), so it is not trusted: {stdout}"
    )]
    UnsoundSat {
        stdout: String,
        rejected: Vec<String>,
    },
    /// Neither `sat`, `unsat`, nor `unknown` could be found as a standalone
    /// line anywhere in the solver's output (or more than one was found),
    /// which is different from the solver itself reporting `unknown`.
    #[error("no verdict found in solver output: {stdout}")]
    NoVerdict { stdout: String },
    #[error("timed out after {0:?}")]
    Timeout(std::time::Duration),
    #[error("io error")]
    Io(#[from] std::io::Error),
}

/// The name of a verdict: `sat`, `unsat`, `timeout`, `unknown` or `error`.
pub fn verdict(result: &Result<(), CheckSatError>) -> &'static str {
    match result {
        Ok(()) => "sat",
        Err(CheckSatError::Unsat) => "unsat",
        Err(CheckSatError::Timeout(_)) => "timeout",
        Err(CheckSatError::Unknown { .. }) => "unknown",
        Err(_) => "error",
    }
}

/// One of the three answers a solver can give `(check-sat)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// Finds the solver's verdict in its raw stdout, tolerating whatever else got
/// printed around it, and separately reports every line that is not the
/// verdict (almost always `unsupported`, once per declaration the solver
/// would not process).
///
/// `(check-sat)` is always the last command Thrust sends, so on a solver that
/// implements everything the query uses, its answer is also the *entire*
/// output. A solver that rejects a `declare-forall-sort` / `declare-forall-fun`
/// / `declare-dep-exists-fun` line does not stop there, though: it prints
/// `unsupported` for that line and keeps processing the rest of the file, so
/// the verdict can be one line among several rather than the whole output.
///
/// Returns `None` when accounting for the output does not come out to
/// exactly one verdict-shaped line: zero means `(check-sat)` was never
/// answered, and more than one means some other line happens to read `sat`,
/// `unsat`, or `unknown`, which makes picking one a guess this function
/// declines to make.
///
/// This does not by itself decide whether a `sat`/`unsat` verdict reached
/// alongside rejected lines should be trusted; [`Config::check_sat`] does,
/// and the two directions are not symmetric. Every rejected line drops
/// whatever the query used it to assert, which can only *relax* the problem
/// (remove a constraint), never add one. Relaxing a problem can only make
/// `sat` easier to reach and `unsat` harder: an `unsat` verdict for the
/// relaxed problem holds for the original, stricter one too (adding back a
/// dropped constraint cannot turn an unsatisfiable problem satisfiable), but
/// a `sat` verdict for the relaxed problem says nothing about the original,
/// because the very constraint that got dropped could be the one the
/// witness violates. So an `unsat` reached this way is safe to accept
/// unconditionally, while a `sat` reached this way is not: accepting it
/// could turn an unprovable program into a verified one.
fn read_verdict(stdout: &str) -> Option<(Verdict, Vec<String>)> {
    let mut verdict = None;
    let mut rejected = Vec::new();
    for line in stdout.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let this_line = match line {
            "sat" => Some(Verdict::Sat),
            "unsat" => Some(Verdict::Unsat),
            "unknown" => Some(Verdict::Unknown),
            _ => None,
        };
        match this_line {
            Some(v) if verdict.is_none() => verdict = Some(v),
            Some(_) => return None,
            None => rejected.push(line.to_owned()),
        }
    }
    verdict.map(|v| (v, rejected))
}

/// What the configured solver reads beyond plain CHC SMT-LIB2, derived once from [`Config`]
/// by [`Config::capabilities`] and carried to the emitter in
/// [`crate::chc::format_context::FormatContext`], so that no other code tests solver names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Capabilities {
    /// The solver reads `declare-dep-exists-fun` (CoAR's PCSat), where a plain `declare-fun`
    /// means "depends on every forall pred declared before it". The default `z3` rejects the
    /// command, and there a plain `declare-fun` is already exact, since z3 has no forall preds.
    pub dependency_aware_declarations: bool,
}

/// A configuration for running a command-line CHC solver.
#[derive(Debug, Clone)]
pub struct CommandConfig {
    pub name: String,
    pub args: Vec<String>,
    pub timeout: Option<std::time::Duration>,
}

impl CommandConfig {
    /// Whether this is the default `z3` binary rather than a solver named by `THRUST_SOLVER`
    /// (in the tests, the PCSat wrapper).
    fn is_z3(&self) -> bool {
        self.name == "z3"
    }

    fn load_args(&mut self, env: &str) {
        if let Ok(args) = std::env::var(env) {
            self.args = args.split_whitespace().map(|s| s.to_owned()).collect();
        }
    }

    fn load_timeout(&mut self, env: &str) {
        if let Ok(timeout) = std::env::var(env) {
            let timeout_secs = timeout.parse().unwrap();
            if timeout_secs == 0 {
                self.timeout = None;
            } else {
                self.timeout = Some(std::time::Duration::from_secs(timeout_secs));
            }
        }
    }

    fn wait_child(
        &self,
        child: std::process::Child,
    ) -> Result<(std::process::Output, std::time::Duration), CheckSatError> {
        use process_control::{ChildExt as _, Control as _};

        let start = std::time::Instant::now();
        let pid = child.id();
        tracing::info!(timeout = ?self.timeout, pid, "waiting");
        let mut child = child.controlled_with_output();
        if let Some(timeout) = self.timeout {
            child = child.time_limit(timeout);
        }
        let output = match child.wait()? {
            None => {
                let pid = nix::unistd::Pid::from_raw(pid as i32);
                if let Err(err) = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGTERM) {
                    tracing::error!(?pid, ?err, "failed to send SIGTERM to solver process");
                }
                return Err(CheckSatError::Timeout(self.timeout.unwrap()));
            }
            Some(output) => output,
        };
        let elapsed = std::time::Instant::now() - start;
        Ok((output.into_std_lossy(), elapsed))
    }

    fn run(
        &self,
        path_arg: impl AsRef<std::path::Path>,
        stdout: impl Into<std::process::Stdio>,
    ) -> Result<String, CheckSatError> {
        let path_arg = path_arg.as_ref();
        let child = std::process::Command::new(&self.name)
            .args(&self.args)
            .arg(path_arg)
            .stdout(stdout)
            .stderr(std::process::Stdio::piped())
            .spawn()?;
        tracing::info!(program = self.name, args = ?self.args, path = %path_arg.to_string_lossy(), pid = child.id(), "spawned");

        let (output, elapsed) = self.wait_child(child)?;
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        tracing::info!(status = %output.status, ?elapsed, "exited");
        if !output.status.success() {
            return Err(CheckSatError::Error {
                stdout: stdout.into_owned(),
                stderr: stderr.into_owned(),
            });
        }
        Ok(stdout.into_owned())
    }
}

/// A configuration for solving a [`crate::chc::System`].
///
/// This struct holds the configuration for the solver, including the solver command, its
/// arguments, and a timeout. It can also be configured to run a preprocessor on the SMT-LIB2
/// file before passing it to the solver.
///
/// The configuration can be loaded from environment variables using [`Config::from_env`].
#[derive(Debug, Clone)]
pub struct Config {
    pub solver: CommandConfig,
    pub preprocessor: Option<CommandConfig>,
    pub output_dir: Option<std::path::PathBuf>,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            solver: CommandConfig {
                name: "z3".to_owned(),
                // Without `fp.engine`, z3 picks its engine from the query, and takes a query over
                // bit-vectors alone for its finite-domain Datalog engine, which enumerates them.
                args: vec![
                    "fp.engine=spacer".to_owned(),
                    "fp.spacer.global=true".to_owned(),
                    "fp.validate=true".to_owned(),
                ],
                timeout: Some(std::time::Duration::from_secs(30)),
            },
            preprocessor: None,
            output_dir: None,
        }
    }
}

impl Config {
    pub fn from_env() -> Config {
        let mut config = Config::default();
        if let Ok(solver) = std::env::var("THRUST_SOLVER") {
            config.solver.name = solver;
        }
        if !config.solver.is_z3() {
            config.solver.args.clear();
        }
        config.solver.load_args("THRUST_SOLVER_ARGS");
        config.solver.load_timeout("THRUST_SOLVER_TIMEOUT_SECS");
        if let Ok(preproc) = std::env::var("THRUST_PREPROCESSOR") {
            let mut preproc_config = CommandConfig {
                name: preproc,
                args: vec![],
                timeout: Some(std::time::Duration::from_secs(30)),
            };
            preproc_config.load_args("THRUST_PREPROCESSOR_ARGS");
            preproc_config.load_timeout("THRUST_PREPROCESSOR_TIMEOUT_SECS");
            config.preprocessor = Some(preproc_config);
        }
        if let Ok(dir) = std::env::var("THRUST_OUTPUT_DIR") {
            config.output_dir = Some(dir.into());
        }
        config
    }

    /// The solver as a verdict depends on it: the command and the preprocessor with their
    /// arguments, and `THRUST_CACHE_SALT`, which the caller sets to what else decides the verdict,
    /// such as the build a solver command runs.
    pub fn identity(&self) -> String {
        let command = |c: &CommandConfig| format!("{} {}", c.name, c.args.join(" "));
        let preprocessor = self.preprocessor.as_ref().map(command).unwrap_or_default();
        let salt = std::env::var("THRUST_CACHE_SALT").unwrap_or_default();
        format!(
            "solver: {}; preprocessor: {preprocessor}; salt: {salt}",
            command(&self.solver)
        )
    }

    /// Writes `query` with its `(check-sat)` to `name` in `THRUST_OUTPUT_DIR`, if it is set.
    pub fn save_query(&self, name: &str, query: &str) -> std::io::Result<()> {
        let Some(dir) = &self.output_dir else {
            return Ok(());
        };
        std::fs::write(dir.join(name), format!("{query}\n(check-sat)\n"))
    }

    pub fn is_z3(&self) -> bool {
        self.solver.is_z3()
    }

    pub fn capabilities(&self) -> Capabilities {
        Capabilities {
            dependency_aware_declarations: !self.solver.is_z3(),
        }
    }

    /// Whether the solver is asked for the evidence `requests` names along with its verdict:
    /// only `z3` is, which prints a model after `(get-model)` and a refutation after
    /// `(get-proof)`.
    pub fn answers(&self, requests: Requests) -> bool {
        (requests.model || requests.proof) && self.solver.is_z3() && self.preprocessor.is_none()
    }

    /// Solves `problem`, also asking for the evidence `requests` names when the solver gives it
    /// (see [`Config::answers`]).
    pub fn check_sat_with(&self, problem: impl std::fmt::Display, requests: Requests) -> Answer {
        let mut answer = Answer::of(Ok(()));
        let evidence = match self.run_check_sat(problem, requests) {
            Ok(output) => {
                let (verdict, evidence) = split_evidence(&output, self.answers(requests));
                answer.result = interpret_verdict(verdict);
                evidence
            }
            Err(err) => {
                answer.result = Err(err);
                Vec::new()
            }
        };
        if answer.result.is_ok() {
            answer.model = evidence.into_iter().find(|e| !e.is_error());
        }
        answer
    }

    /// What `z3` prints for `script`, when the solver is `z3`; also when some command of the script
    /// failed, which `z3` reports in its output.
    pub fn run_script(&self, script: &str) -> Option<String> {
        use std::io::Write as _;
        if !self.solver.is_z3() {
            return None;
        }
        let mut file = tempfile::Builder::new()
            .prefix("thrust_tmp_")
            .suffix(".smt2")
            .tempfile()
            .ok()?;
        file.write_all(script.as_bytes()).ok()?;
        file.flush().ok()?;
        match self.solver.run(file.path(), std::process::Stdio::piped()) {
            Ok(output) | Err(CheckSatError::Error { stdout: output, .. }) => Some(output),
            Err(_) => None,
        }
    }

    /// `z3`'s refutation of `problem`, which it answers `unsat`, by Spacer, whose refutations are
    /// hyper-resolutions. Its preprocessing would fold clauses into one another, and with them
    /// the facts the refutation derives, and drop the premises a fact makes true, so the
    /// transformations doing so are turned off.
    pub fn refute(&self, problem: impl std::fmt::Display) -> Option<Sexp> {
        use std::io::Write as _;
        let mut file = tempfile::Builder::new()
            .prefix("thrust_tmp_")
            .suffix(".smt2")
            .tempfile()
            .ok()?;
        write!(file, "{problem}\n(check-sat)\n(get-proof)\n").ok()?;
        file.flush().ok()?;
        let mut solver = self.solver.clone();
        solver.args.extend(
            [
                "proof=true",
                "fp.engine=spacer",
                "fp.xform.slice=false",
                "fp.xform.inline_linear=false",
                "fp.xform.inline_eager=false",
                "fp.xform.subsumption_checker=false",
            ]
            .map(str::to_owned),
        );
        let output = solver.run(file.path(), std::process::Stdio::piped()).ok()?;
        let (verdict, evidence) = split_evidence(&output, true);
        if read_verdict(&verdict)?.0 != Verdict::Unsat {
            return None;
        }
        evidence.into_iter().find(|e| !e.is_error())
    }

    fn run_check_sat(
        &self,
        problem: impl std::fmt::Display,
        requests: Requests,
    ) -> Result<String, CheckSatError> {
        use std::io::{Seek as _, Write as _};
        let smt2 = format!("{}\n(check-sat)\n", problem);
        let mut file = tempfile::Builder::new()
            .prefix("thrust_tmp_")
            .suffix(".smt2")
            .tempfile()?;
        write!(file, "{}", smt2)?;
        file.flush()?;
        let answers = self.answers(requests);
        if answers && requests.model {
            writeln!(file, "(get-model)")?;
            file.flush()?;
        }

        if let Some(preproc) = &self.preprocessor {
            let output = preproc.run(file.path(), std::process::Stdio::piped())?;
            file.as_file_mut().set_len(0)?;
            file.rewind()?;
            write!(file, "{}", output)?;
            if let Some(dir) = &self.output_dir {
                std::fs::copy(&file, dir.join("preproc_output.smt2"))?;
            }
        }

        let output = self.solver.run(file.path(), std::process::Stdio::piped());
        drop(file);
        match output {
            // `z3` exits with an error when it cannot answer `(get-model)` after `unsat` or
            // `(get-proof)` after `sat`, having printed the verdict. An error before the verdict
            // (a line of the query it could not read) is an error whatever was asked, so that
            // the verdict does not depend on the report.
            Err(CheckSatError::Error { stdout, .. })
                if answers && only_evidence_failed(&stdout) =>
            {
                Ok(stdout)
            }
            output => output,
        }
    }
}

/// What a caller wants besides the verdict.
#[derive(Debug, Clone, Copy, Default)]
pub struct Requests {
    /// The model of a `sat` answer: an interpretation of each predicate variable.
    pub model: bool,
    /// The refutation of an `unsat` answer.
    pub proof: bool,
}

/// The verdict, with the model of a `sat` answer or the refutation of an `unsat` one as the
/// solver printed them, read as s-expressions, if asked for and given.
#[derive(Debug)]
pub struct Answer {
    pub result: Result<(), CheckSatError>,
    pub model: Option<Sexp>,
    pub proof: Option<Sexp>,
    /// The predicate variable marking each goal of the system in the query, when a refutation
    /// is asked for (see [`crate::chc::System::solve_with`]).
    pub goal_markers: Vec<(crate::chc::PredVarId, crate::chc::ClauseId)>,
    /// The predicate variable tagging each clause of the system in the refutation's query.
    pub clause_tags: Vec<(crate::chc::PredVarId, crate::chc::ClauseId)>,
    /// The query, when a model is asked for: its declarations are what the model's terms are
    /// over.
    pub query: Option<String>,
}

impl Answer {
    /// The verdict `result`, without evidence.
    pub fn of(result: Result<(), CheckSatError>) -> Self {
        Answer {
            result,
            model: None,
            proof: None,
            goal_markers: Vec::new(),
            clause_tags: Vec::new(),
            query: None,
        }
    }
}

/// Splits the solver's output into the part with the verdict and the s-expressions printed after
/// it, which are the answers to `(get-model)` and `(get-proof)` when `asked`.
fn split_evidence(output: &str, asked: bool) -> (String, Vec<Sexp>) {
    if !asked {
        return (output.to_owned(), Vec::new());
    }
    let verdict_end = output
        .lines()
        .position(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"));
    let Some(verdict_end) = verdict_end else {
        return (output.to_owned(), Vec::new());
    };
    let lines: Vec<&str> = output.lines().collect();
    let verdict = lines[..=verdict_end].join("\n");
    let rest = lines[verdict_end + 1..].join("\n");
    (verdict, super::sexp::parse_all(&rest))
}

/// Whether `stdout` has a verdict and no `(error …)` line before it: only the evidence asked after
/// the verdict failed.
fn only_evidence_failed(stdout: &str) -> bool {
    let (verdict, _) = split_evidence(stdout, true);
    read_verdict(&verdict)
        .is_some_and(|(_, rejected)| rejected.iter().all(|line| !line.starts_with("(error")))
}

fn interpret_verdict(output: String) -> Result<(), CheckSatError> {
    match read_verdict(&output) {
        Some((Verdict::Sat, rejected)) if rejected.is_empty() => Ok(()),
        Some((Verdict::Sat, rejected)) => {
            tracing::warn!(
                ?rejected,
                "solver reported sat after rejecting part of the query; not trusting it"
            );
            Err(CheckSatError::UnsoundSat {
                stdout: output,
                rejected,
            })
        }
        Some((Verdict::Unsat, rejected)) => {
            if !rejected.is_empty() {
                tracing::warn!(
                    ?rejected,
                    "solver reported unsat after rejecting part of the query; \
                         accepting it, since dropping constraints cannot turn an \
                         unsatisfiable problem satisfiable"
                );
            }
            Err(CheckSatError::Unsat)
        }
        Some((Verdict::Unknown, rejected)) => {
            if !rejected.is_empty() {
                tracing::warn!(?rejected, "solver reported unknown, alongside other output");
            }
            Err(CheckSatError::Unknown { stdout: output })
        }
        None => Err(CheckSatError::NoVerdict { stdout: output }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn evidence_follows_the_verdict() {
        let output = "sat\n(\n  (define-fun p0 ((x!0 Int)) Bool\n    (>= x!0 0))\n)\n(error \"line 9 column 0: proof is not available\")\n";
        let (verdict, evidence) = split_evidence(output, true);
        assert_eq!(verdict, "sat");
        assert_eq!(evidence.len(), 2);
        assert!(evidence[0].to_string().contains("define-fun p0"));
        assert!(evidence[1].is_error());
        let (verdict, evidence) = split_evidence(output, false);
        assert_eq!(verdict, output);
        assert!(evidence.is_empty());
    }

    #[test]
    fn clean_verdicts_have_nothing_rejected() {
        assert_eq!(read_verdict("sat\n"), Some((Verdict::Sat, vec![])));
        assert_eq!(read_verdict("unsat\n"), Some((Verdict::Unsat, vec![])));
        assert_eq!(read_verdict("unknown\n"), Some((Verdict::Unknown, vec![])));
    }

    #[test]
    fn verdict_can_follow_rejected_lines() {
        assert_eq!(
            read_verdict("unsupported\nunsupported\nsat\n"),
            Some((
                Verdict::Sat,
                vec!["unsupported".into(), "unsupported".into()]
            ))
        );
        assert_eq!(
            read_verdict("unsupported\nunsat\n"),
            Some((Verdict::Unsat, vec!["unsupported".into()]))
        );
    }

    #[test]
    fn no_verdict_line_is_not_a_verdict() {
        assert_eq!(read_verdict(""), None);
        assert_eq!(read_verdict("unsupported\n"), None);
        assert_eq!(read_verdict("(error \"boom\")\n"), None);
    }

    #[test]
    fn conflicting_verdict_lines_are_not_a_verdict() {
        assert_eq!(read_verdict("sat\nunsat\n"), None);
        assert_eq!(read_verdict("unsat\nunsat\n"), None);
    }
}
