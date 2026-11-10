//! Verdicts of earlier runs by query (`THRUST_CACHE_DIR`), so that a query that has not changed is
//! not solved again.
//!
//! A query is keyed by its text with the comments left out and the unknowns renamed in the order
//! they first occur, so that numbering the unknowns of other parts of the crate differently does
//! not change the key (other numbered symbols, such as the forall sorts, still do), and by the
//! solver it is given to ([`Config::identity`]). An entry keeps the text it was stored for, and a
//! lookup compares it, so two queries with one hash are never confused; a file name from another
//! toolchain's hasher only misses. Only `sat` and `unsat` are kept; a timeout or an unknown is
//! solved again. Entries are never removed.
//!
//! The key leaves out the solver's time limit and the resources it runs with, so a verdict is
//! reused across them. An entry therefore records, apart from the key, how it was found
//! ([`Provenance`]), so that the verdict can be reproduced.

use std::collections::HashMap;
use std::hash::{Hash as _, Hasher as _};
use std::path::PathBuf;

use super::solver::{CheckSatError, Config, Requests};

pub struct Cache {
    dir: PathBuf,
}

/// The environment variables that the solver wrappers read for the resources and the
/// configuration a solver runs with. Only the solver wrappers read them, not Thrust, so the
/// `THRUST_` names are written with `concat!` to stay out of `crate::ENV_VARS`.
const SOLVER_SETTINGS: [&str; 5] = [
    concat!("THRUST_", "PCSAT_CPUS"),
    concat!("THRUST_", "PCSAT_MEMORY"),
    "COAR_IMAGE",
    "COAR_CONFIG",
    "COAR_CONFIG_DIR",
];

/// Marks a line of an entry that tells how the verdict was found and is not part of the key.
const PROVENANCE_PREFIX: &str = "; found: ";

/// How a stored verdict was obtained: the lines `; found: <name>: <value>` of its entry.
pub struct Provenance(Vec<(&'static str, String)>);

impl Provenance {
    /// The circumstances of a solve that took `wall` and ended just now, under the settings of
    /// this process.
    pub fn of_solve(wall: std::time::Duration, timeout: Option<std::time::Duration>) -> Self {
        let mut fields = vec![
            ("wall_secs", format!("{:.3}", wall.as_secs_f64())),
            ("date", utc_date_time(std::time::SystemTime::now())),
            (
                "timeout_secs",
                timeout.map_or(0, |t| t.as_secs()).to_string(),
            ),
            ("thrust_version", env!("CARGO_PKG_VERSION").to_owned()),
        ];
        for name in SOLVER_SETTINGS {
            let value = std::env::var(name).unwrap_or_else(|_| "unset".to_owned());
            fields.push((name, value));
        }
        Provenance(fields)
    }

    fn to_lines(&self) -> String {
        let line = |(name, value): &(&str, String)| format!("{PROVENANCE_PREFIX}{name}: {value}\n");
        self.0.iter().map(line).collect()
    }
}

impl std::fmt::Display for Provenance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let fields: Vec<_> = self.0.iter().map(|(n, v)| format!("{n}={v}")).collect();
        f.write_str(&fields.join(" "))
    }
}

/// `time` as `YYYY-MM-DDTHH:MM:SSZ` (UTC).
fn utc_date_time(time: std::time::SystemTime) -> String {
    let secs = time
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs());
    let (days, rest) = ((secs / 86400) as i64, secs % 86400);
    // Civil date from days since 1970-01-01 (Howard Hinnant's algorithm).
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z.rem_euclid(146097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}Z",
        rest / 3600,
        rest % 3600 / 60,
        rest % 60
    )
}

/// The entry text after its verdict line: the provenance lines, then the key.
fn split_provenance(text: &str) -> (String, &str) {
    let mut provenance = String::new();
    let mut rest = text;
    while let Some(line) = rest
        .split_inclusive('\n')
        .next()
        .filter(|l| l.starts_with(PROVENANCE_PREFIX))
    {
        provenance.push_str(line[PROVENANCE_PREFIX.len()..].trim_end());
        provenance.push(' ');
        rest = &rest[line.len()..];
    }
    (provenance, rest)
}

fn is_unknown_symbol(token: &str) -> bool {
    token
        .strip_prefix('p')
        .is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
}

/// `query` without its comments and with each unknown `p<n>` renamed `p<k>`, `k` the order of its
/// first occurrence.
pub fn canonical(query: &str) -> String {
    let mut renamed: HashMap<String, String> = HashMap::new();
    let mut out = String::with_capacity(query.len());
    for line in query.lines() {
        if line.trim_start().starts_with(';') || line.trim().is_empty() {
            continue;
        }
        let mut token = String::new();
        for c in line.chars().chain(std::iter::once('\n')) {
            if c == '(' || c == ')' || c.is_whitespace() {
                if is_unknown_symbol(&token) {
                    let next = format!("p{}", renamed.len());
                    out.push_str(renamed.entry(token.clone()).or_insert(next));
                } else {
                    out.push_str(&token);
                }
                token.clear();
                out.push(c);
            } else {
                token.push(c);
            }
        }
    }
    out
}

impl Cache {
    pub fn from_env() -> Option<Self> {
        let dir = PathBuf::from(std::env::var_os("THRUST_CACHE_DIR")?);
        if let Err(err) = std::fs::create_dir_all(&dir) {
            tracing::warn!(?err, dir = %dir.display(), "no verdicts are kept");
            return None;
        }
        Some(Cache { dir })
    }

    fn entry(&self, key: &str) -> PathBuf {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key.hash(&mut hasher);
        self.dir.join(format!("{:016x}", hasher.finish()))
    }

    /// The key of `query` given to `solver`, a description of the solver and its configuration.
    pub fn key(query: &str, solver: &str) -> String {
        format!("; solver: {solver}\n{}", canonical(query))
    }

    pub fn lookup(&self, key: &str) -> Option<Result<(), CheckSatError>> {
        let stored = std::fs::read_to_string(self.entry(key)).ok()?;
        let (verdict, text) = stored.split_once('\n')?;
        let (provenance, stored_key) = split_provenance(text);
        if stored_key != key {
            return None;
        }
        let result = match verdict {
            "sat" => Ok(()),
            "unsat" => Err(CheckSatError::Unsat),
            _ => return None,
        };
        let provenance = provenance.trim_end();
        let provenance = if provenance.is_empty() {
            "not recorded"
        } else {
            provenance
        };
        tracing::debug!(verdict, found = provenance, "verdict taken from the cache");
        Some(result)
    }

    pub fn store(&self, key: &str, result: &Result<(), CheckSatError>, found: &Provenance) {
        let verdict = super::solver::verdict(result);
        if !matches!(verdict, "sat" | "unsat") {
            return;
        }
        use std::io::Write as _;
        let path = self.entry(key);
        // Written whole to a file of its own, then renamed, so that a reader or another writer of
        // the entry never sees a part of it.
        let written = tempfile::NamedTempFile::new_in(&self.dir).and_then(|mut file| {
            write!(file, "{verdict}\n{}{key}", found.to_lines())?;
            file.persist(&path).map_err(|err| err.error)?;
            Ok(())
        });
        if let Err(err) = written {
            tracing::warn!(?err, path = %path.display(), "could not store a verdict");
        }
    }
}

/// A verdict, and whether it was that of an earlier run.
pub struct Verdict {
    pub result: Result<(), CheckSatError>,
    pub cached: bool,
}

/// The verdict of `config`'s solver on `query`, from `cache` when it keeps one.
pub fn solve(config: &Config, cache: Option<&Cache>, query: &str) -> Verdict {
    let check_sat = || config.check_sat_with(query, Requests::default()).result;
    let Some(cache) = cache else {
        return Verdict {
            result: check_sat(),
            cached: false,
        };
    };
    let key = Cache::key(query, &config.identity());
    if let Some(result) = cache.lookup(&key) {
        return Verdict {
            result,
            cached: true,
        };
    }
    let started = std::time::Instant::now();
    let result = check_sat();
    let found = Provenance::of_solve(started.elapsed(), config.solver.timeout);
    cache.store(&key, &result, &found);
    Verdict {
        result,
        cached: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn found() -> Provenance {
        Provenance::of_solve(std::time::Duration::from_millis(1500), None)
    }

    fn cache_in(dir: &tempfile::TempDir) -> Cache {
        Cache {
            dir: dir.path().to_owned(),
        }
    }

    #[test]
    fn entry_records_how_the_verdict_was_found() {
        let dir = tempfile::tempdir().unwrap();
        let cache = cache_in(&dir);
        let key = Cache::key("(assert true)", "z3");
        cache.store(&key, &Ok(()), &found());
        let text = std::fs::read_to_string(cache.entry(&key)).unwrap();
        assert!(text.starts_with("sat\n; found: wall_secs: 1.500\n; found: date: 20"));
        assert!(text.contains("; found: COAR_IMAGE: "));
        assert!(text.ends_with(&key));
        assert!(matches!(cache.lookup(&key), Some(Ok(()))));
        assert!(cache.lookup(&Cache::key("(assert false)", "z3")).is_none());
    }

    #[test]
    fn entry_without_provenance_is_still_read() {
        let dir = tempfile::tempdir().unwrap();
        let cache = cache_in(&dir);
        let key = Cache::key("(assert true)", "z3");
        std::fs::write(cache.entry(&key), format!("unsat\n{key}")).unwrap();
        assert!(matches!(
            cache.lookup(&key),
            Some(Err(CheckSatError::Unsat))
        ));
        assert!(cache
            .lookup(&Cache::key("(assert true)", "other"))
            .is_none());
    }

    #[test]
    fn date_is_utc_iso_8601() {
        let time = std::time::UNIX_EPOCH + std::time::Duration::from_secs(1_794_000_000);
        assert_eq!(utc_date_time(time), "2026-11-06T21:20:00Z");
        assert_eq!(utc_date_time(std::time::UNIX_EPOCH), "1970-01-01T00:00:00Z");
    }

    #[test]
    fn canonical_renames_unknowns_by_first_occurrence() {
        let a = "; c0\n(declare-fun p7 (Int) Bool)\n(assert (=> (p7 x) (p12 x)))\n";
        let b = "(declare-fun p3 (Int) Bool)\n\n(assert (=> (p3 x) (p40 x)))\n";
        assert_eq!(canonical(a), canonical(b));
        assert_eq!(
            canonical(a),
            "(declare-fun p0 (Int) Bool)\n(assert (=> (p0 x) (p1 x)))\n"
        );
        let c = "(declare-fun p3 (Int) Bool)\n(assert (=> (p40 x) (p3 x)))\n";
        assert_ne!(canonical(a), canonical(c));
    }

    #[test]
    fn keeps_only_sat_and_unsat() {
        let dir = tempfile::tempdir().unwrap();
        let cache = Cache {
            dir: dir.path().to_owned(),
        };
        let key = Cache::key("(assert true)", "z3");
        assert!(cache.lookup(&key).is_none());
        cache.store(
            &key,
            &Err(CheckSatError::Timeout(std::time::Duration::from_secs(1))),
            &found(),
        );
        assert!(cache.lookup(&key).is_none());
        cache.store(&key, &Err(CheckSatError::Unsat), &found());
        assert!(matches!(
            cache.lookup(&key),
            Some(Err(CheckSatError::Unsat))
        ));
        assert!(cache
            .lookup(&Cache::key("(assert true)", "other"))
            .is_none());
    }
}
