//! A generic interface for running external command-line CHC solvers.
//!
//! This module provides the [`Config`] struct for configuring and running an external
//! CHC solver. It supports setting the solver command, arguments, and timeout, and can
//! be configured through environment variables.

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
                args: vec![
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

    pub fn capabilities(&self) -> Capabilities {
        Capabilities {
            dependency_aware_declarations: !self.solver.is_z3(),
        }
    }

    pub fn check_sat(&self, problem: impl std::fmt::Display) -> Result<(), CheckSatError> {
        use std::io::{Seek as _, Write as _};
        let smt2 = format!("{}\n(check-sat)\n", problem);
        let mut file = tempfile::Builder::new()
            .prefix("thrust_tmp_")
            .suffix(".smt2")
            .tempfile()?;
        write!(file, "{}", smt2)?;
        file.flush()?;
        if let Some(dir) = &self.output_dir {
            std::fs::copy(&file, dir.join("thrust_output.smt2"))?;
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

        let output = self.solver.run(file.path(), std::process::Stdio::piped())?;
        drop(file);
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
}

#[cfg(test)]
mod tests {
    use super::*;

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
