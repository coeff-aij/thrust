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

use std::collections::HashMap;
use std::hash::{Hash as _, Hasher as _};
use std::path::PathBuf;

use super::solver::{CheckSatError, Config, Requests};

pub struct Cache {
    dir: PathBuf,
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
        if text != key {
            return None;
        }
        match verdict {
            "sat" => Some(Ok(())),
            "unsat" => Some(Err(CheckSatError::Unsat)),
            _ => None,
        }
    }

    pub fn store(&self, key: &str, result: &Result<(), CheckSatError>) {
        let verdict = match result {
            Ok(()) => "sat",
            Err(CheckSatError::Unsat) => "unsat",
            Err(_) => return,
        };
        use std::io::Write as _;
        let path = self.entry(key);
        // Written whole to a file of its own, then renamed, so that a reader or another writer of
        // the entry never sees a part of it.
        let written = tempfile::NamedTempFile::new_in(&self.dir).and_then(|mut file| {
            write!(file, "{verdict}\n{key}")?;
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
    let result = check_sat();
    cache.store(&key, &result);
    Verdict {
        result,
        cached: false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        );
        assert!(cache.lookup(&key).is_none());
        cache.store(&key, &Err(CheckSatError::Unsat));
        assert!(matches!(
            cache.lookup(&key),
            Some(Err(CheckSatError::Unsat))
        ));
        assert!(cache
            .lookup(&Cache::key("(assert true)", "other"))
            .is_none());
    }
}
