#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
#[cfg(test)]
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;

// works with MIR
mod analyze;

// TODO: remove refine module
mod refine;

// pure logic
mod chc;
mod rty;

// utility
mod pretty;

// user-facing output
mod report;

pub use analyze::mir_borrowck_skip_formula_fn;
pub use analyze::Analyzer;
pub use chc::debug::SpanFieldsLayer;

/// The file name `std.rs` is parsed under when it is injected into the analyzed crate.
pub const INJECTED_STD_FILE_NAME: &str = "thrust std injected";

/// The environment variables a run of Thrust reads, which decide its result. The driver records
/// them in the crate's dep-info, so that cargo checks a crate again when one of them changes.
pub const ENV_VARS: &[&str] = &[
    "THRUST_CACHE_DIR",
    "THRUST_CACHE_SALT",
    "THRUST_CANDIDATE_ATOMS",
    "THRUST_CHECK_UINT_FACTS",
    "THRUST_DEDUP_PRED_ARGS",
    "THRUST_ENUM_EXPANSION_DEPTH_LIMIT",
    "THRUST_FLAT_PRED_ARGS",
    "THRUST_INT_RANGE",
    "THRUST_NO_INJECT_STD",
    "THRUST_OPTIMIZED_MIR",
    "THRUST_OUTPUT_DIR",
    "THRUST_PER_INSTANCE_GENERICS",
    "THRUST_PREPROCESSOR",
    "THRUST_PREPROCESSOR_ARGS",
    "THRUST_PREPROCESSOR_TIMEOUT_SECS",
    "THRUST_PRETTY_OUTPUT",
    "THRUST_REPORT",
    "THRUST_REPORT_FILE",
    "THRUST_REPORT_FORMAT",
    "THRUST_REPORT_ONLY",
    "THRUST_SOLVER",
    "THRUST_SOLVER_ARGS",
    "THRUST_SOLVER_TIMEOUT_SECS",
    "THRUST_SPLIT",
    "THRUST_TRY_SPECS",
    "THRUST_UNSPECIFIED_UNREACHABLE",
    "THRUST_VERIFY_ONLY",
];

#[cfg(test)]
mod tests {
    /// [`super::ENV_VARS`] lists the `THRUST_` variables the sources other than this file name.
    #[test]
    fn env_vars_lists_every_variable_read() {
        let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
        let mut named = std::collections::BTreeSet::new();
        let mut dirs = vec![src];
        while let Some(dir) = dirs.pop() {
            for entry in std::fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    dirs.push(path);
                    continue;
                }
                if path.ends_with("src/lib.rs") {
                    continue;
                }
                let text = std::fs::read_to_string(&path).unwrap();
                for literal in text.split("\"THRUST_").skip(1) {
                    let name: String = literal
                        .chars()
                        .take_while(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || *c == '_')
                        .collect();
                    if !name.is_empty() && literal[name.len()..].starts_with('"') {
                        named.insert(format!("THRUST_{name}"));
                    }
                }
            }
        }
        let listed: std::collections::BTreeSet<String> =
            super::ENV_VARS.iter().map(|v| v.to_string()).collect();
        assert_eq!(named, listed);
    }
}
