#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};

fn try_specs_enabled() -> bool {
    matches!(std::env::var("THRUST_TRY_SPECS").as_deref(), Ok("1"))
}

/// Whether `THRUST_INT_RANGE` is set: the injected `std.rs` then models a `w`-bit unsigned type
/// as `UIntN<w>` (under `cfg(thrust_int_range)`) instead of `UInt`.
fn int_range_enabled() -> bool {
    std::env::var_os("THRUST_INT_RANGE").is_some()
}

struct CompilerCalls {}

impl Callbacks for CompilerCalls {
    fn config(&mut self, config: &mut Config) {
        let attrs = &mut config.opts.unstable_opts.crate_attr;
        attrs.push("feature(register_tool)".to_owned());
        if try_specs_enabled() {
            attrs.push("feature(try_trait_v2)".to_owned());
        }
        attrs.push("register_tool(thrust)".to_owned());
        config
            .crate_check_cfg
            .push("cfg(thrust_int_range)".to_owned());
        if int_range_enabled() {
            config.crate_cfg.push("thrust_int_range".to_owned());
        }

        // Refinements live on MIR locals, and `RemoveZsts` rewrites reads of zero-sized
        // locals into constants, losing the refinement of every value whose type carries
        // no runtime data -- the model types and `Ghost<T>`.
        config
            .opts
            .unstable_opts
            .mir_enable_passes
            .push(("RemoveZsts".to_owned(), false));

        // With UB checks on, these passes insert null and alignment checks before every
        // dereference of a raw pointer, which includes each `Box` dereference once
        // `ElaborateBoxDerefs` has run. A `Box` pointer is always non-null and aligned, and
        // the checks go through pointer-to-integer casts that Thrust does not model.
        for pass in ["CheckAlignment", "CheckNull"] {
            config
                .opts
                .unstable_opts
                .mir_enable_passes
                .push((pass.to_owned(), false));
        }

        config.override_queries = Some(|_sess, providers| {
            providers.mir_borrowck = thrust::mir_borrowck_skip_formula_fn;
        });
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &Compiler,
        krate: &mut rustc_ast::Crate,
    ) -> Compilation {
        if matches!(std::env::var("THRUST_NO_INJECT_STD").as_deref(), Ok("1")) {
            return Compilation::Continue;
        }

        let mut injected = include_str!("../std.rs").to_owned();
        if try_specs_enabled() {
            injected.push_str(include_str!("../std_try.rs"));
        }
        let mut parser = rustc_parse::new_parser_from_source_str(
            &compiler.sess.psess,
            rustc_span::FileName::Custom(thrust::INJECTED_STD_FILE_NAME.to_string()),
            injected,
        )
        .unwrap();
        while let Some(item) = parser
            .parse_item(rustc_parse::parser::ForceCollect::No)
            .unwrap()
        {
            krate.items.push(item);
        }
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> Compilation {
        let mut ctx = thrust::Analyzer::new(tcx);
        ctx.register_well_known_defs();
        ctx.crate_analyzer().run();
        ctx.solve();
        Compilation::Stop
    }
}

/// The thrust-macros library to link the analyzed crate with: the build this binary was compiled
/// against, or, when that is gone (the binary was moved), the newest build next to the binary.
fn thrust_macros_path() -> Option<std::path::PathBuf> {
    let linked = std::path::Path::new(thrust_macros::linked_path!());
    if linked.is_file() {
        return Some(linked.to_path_buf());
    }
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?;
    // When thrust-macros is a cargo dependency it lands in deps/ with a hash
    // suffix (e.g. libthrust_macros-<hash>.so).
    [dir.to_path_buf(), dir.join("deps")]
        .iter()
        .filter_map(|search_dir| std::fs::read_dir(search_dir).ok())
        .flatten()
        .flatten()
        .filter(|entry| {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            name.starts_with("libthrust_macros")
                && ["so", "dylib", "dll"]
                    .iter()
                    .any(|ext| name.ends_with(&format!(".{ext}")))
        })
        .max_by_key(|entry| entry.metadata().and_then(|m| m.modified()).ok())
        .map(|entry| entry.path())
}

pub fn main() {
    let mut args = std::env::args().collect::<Vec<_>>();

    use tracing_subscriber::{filter::EnvFilter, prelude::*};
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_writer(std::io::stderr)
                .compact()
                .without_time()
                .with_filter(EnvFilter::from_default_env()),
        )
        .init();

    if let Some(path) = thrust_macros_path() {
        args.push("--extern".to_owned());
        args.push(format!("thrust_macros={}", path.display()));
        tracing::debug!("linking thrust_macros from {}", path.display());
    } else {
        tracing::warn!("could not locate thrust_macros library");
    }

    let code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut CompilerCalls {})
    });
    std::process::exit(code);
}
