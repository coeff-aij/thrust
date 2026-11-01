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
use rustc_session::config::OutputType;

fn try_specs_enabled() -> bool {
    matches!(std::env::var("THRUST_TRY_SPECS").as_deref(), Ok("1"))
}

/// Whether `THRUST_INT_RANGE` is set: the injected `std.rs` then models a `w`-bit unsigned type
/// as `UIntN<w>` (under `cfg(thrust_int_range)`) instead of `UInt`.
fn int_range_enabled() -> bool {
    std::env::var_os("THRUST_INT_RANGE").is_some()
}

/// Whether `THRUST_OPTIMIZED_MIR` is set to `1`: Thrust then analyzes the MIR of the optimization
/// level the command line asks for instead of the MIR of `-C opt-level=0`.
fn optimized_mir_enabled() -> bool {
    matches!(std::env::var("THRUST_OPTIMIZED_MIR").as_deref(), Ok("1"))
}

struct CompilerCalls {}

impl Callbacks for CompilerCalls {
    fn config(&mut self, config: &mut Config) {
        let attrs = &mut config.opts.unstable_opts.crate_attr;
        attrs.push("feature(register_tool)".to_owned());
        attrs.push("feature(marker_trait_attr)".to_owned());
        if try_specs_enabled() {
            attrs.push("feature(try_trait_v2)".to_owned());
        }
        attrs.push("register_tool(thrust)".to_owned());
        // std.rs specifies an operation that panics on overflow only with overflow checks on
        // (`Iterator::sum`) by `cfg(overflow_checks)`.
        attrs.push("feature(cfg_overflow_checks)".to_owned());
        config
            .crate_check_cfg
            .push("cfg(thrust_int_range)".to_owned());
        config
            .crate_check_cfg
            .push("cfg(thrust_std_conformance)".to_owned());
        if int_range_enabled() {
            config.crate_cfg.push("thrust_int_range".to_owned());
        }

        // The MIR optimizations preserve the meaning of a program without undefined behaviour
        // and only reshape its MIR. `debug_assertions`, the default of the overflow and UB
        // checks, is settled from the command line before this callback runs.
        if !optimized_mir_enabled() {
            config.opts.optimize = rustc_session::config::OptLevel::No;
            config.opts.unstable_opts.mir_opt_level = None;
            config.opts.unstable_opts.mir_enable_passes.clear();
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

        // Thrust reads each body as written: an inlined callee's body would be analyzed under the
        // caller's mode (a verified generic function inlined into a trusted one), whatever the
        // optimization level.
        config.opts.unstable_opts.inline_mir = Some(false);

        config.override_queries = Some(|_sess, providers| {
            providers.mir_borrowck = thrust::mir_borrowck_skip_formula_fn;
        });

        // The dep-info is written before the analysis, as clippy-driver records `CLIPPY_ARGS`.
        config.psess_created = Some(Box::new(track_inputs));

        // The analysis of a crate using this one reads the MIR of the functions it calls here.
        if only_metadata(&config.opts) {
            config.opts.unstable_opts.always_encode_mir = true;
        }
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
        // The program's own lints are not about the injected items.
        let allow_warnings = |span| allow_warnings(&compiler.sess.psess.attr_id_generator, span);
        while let Some(mut item) = parser
            .parse_item(rustc_parse::parser::ForceCollect::No)
            .unwrap()
        {
            // An attribute on a macro call is ignored; its expansion is not warned about.
            if !matches!(item.kind, rustc_ast::ItemKind::MacCall(_)) {
                item.attrs.push(allow_warnings(item.span));
            }
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
        // `cargo check` of a crate that verifies writes its metadata; no code is generated with
        // the MIR passes turned off above.
        if tcx.dcx().has_errors().is_some() || !only_metadata(&tcx.sess.opts) {
            return Compilation::Stop;
        }
        Compilation::Continue
    }
}

/// Whether the compilation emits only metadata and dep-info.
fn only_metadata(opts: &rustc_session::config::Options) -> bool {
    opts.output_types
        .keys()
        .all(|t| matches!(t, OutputType::Metadata | OutputType::DepInfo))
}

/// Records in the dep-info the variables the run reads, with their values, the Thrust binary and
/// the thrust-macros library, so that cargo checks the crate again when one of them changes.
fn track_inputs(psess: &mut rustc_session::parse::ParseSess) {
    let env_depinfo = psess.env_depinfo.get_mut();
    for var in thrust::ENV_VARS {
        let value = std::env::var(var).ok();
        env_depinfo.insert((
            rustc_span::Symbol::intern(var),
            value.as_deref().map(rustc_span::Symbol::intern),
        ));
    }
    let files = [std::env::current_exe().ok(), thrust_macros_path()];
    for file in files.iter().flatten().filter_map(|f| f.to_str()) {
        psess
            .file_depinfo
            .get_mut()
            .insert(rustc_span::Symbol::intern(file));
    }
}

/// `#[allow(warnings)]` at `span`, with the tokens an attribute needs before expansion (a derive
/// or a `cfg` on the item it is put on reads them).
fn allow_warnings(
    g: &rustc_ast::attr::AttrIdGenerator,
    span: rustc_span::Span,
) -> rustc_ast::Attribute {
    use rustc_ast::token::{Delimiter, Token, TokenKind};
    use rustc_ast::tokenstream::{
        AttrTokenStream, AttrTokenTree, DelimSpacing, DelimSpan, LazyAttrTokenStream, Spacing,
    };
    let ident = |name: &str| {
        let ident = rustc_span::Ident::new(rustc_span::Symbol::intern(name), span);
        AttrTokenTree::Token(Token::from_ast_ident(ident), Spacing::Alone)
    };
    let delimited = |delimiter, inner: Vec<AttrTokenTree>| {
        AttrTokenTree::Delimited(
            DelimSpan::from_single(span),
            DelimSpacing::new(Spacing::Alone, Spacing::Alone),
            delimiter,
            AttrTokenStream::new(inner),
        )
    };
    let tokens = AttrTokenStream::new(vec![
        AttrTokenTree::Token(Token::new(TokenKind::Pound, span), Spacing::Joint),
        delimited(
            Delimiter::Bracket,
            vec![
                ident("allow"),
                delimited(Delimiter::Parenthesis, vec![ident("warnings")]),
            ],
        ),
    ]);
    let mut attr = rustc_ast::attr::mk_attr_nested_word(
        g,
        rustc_ast::AttrStyle::Outer,
        rustc_ast::Safety::Default,
        rustc_span::sym::allow,
        rustc_span::Symbol::intern("warnings"),
        span,
    );
    if let rustc_ast::AttrKind::Normal(normal) = &mut attr.kind {
        normal.tokens = Some(LazyAttrTokenStream::new_direct(tokens));
    }
    attr
}

/// The thrust-macros library to link the analyzed crate with: the most recently modified build
/// next to the binary.
fn thrust_macros_path() -> Option<std::path::PathBuf> {
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

/// Writes log events to stderr with the continuation lines of an event indented. An event spans
/// several lines when a field's pretty-printed value does, and under `--error-format=json` a line
/// that starts with `{` is read as one of rustc's JSON diagnostics.
struct LogWriter;

impl std::io::Write for LogWriter {
    /// Takes `buf` as whole events, as the `fmt` layer writes each event with one `write_all`.
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let (body, end) = match buf.strip_suffix(b"\n") {
            Some(body) => (body, &b"\n"[..]),
            None => (buf, &b""[..]),
        };
        let mut out = Vec::with_capacity(buf.len());
        for (i, line) in body.split(|&b| b == b'\n').enumerate() {
            if i > 0 {
                out.extend_from_slice(b"\n    ");
            }
            out.extend_from_slice(line);
        }
        out.extend_from_slice(end);
        std::io::stderr().write_all(&out)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        std::io::stderr().flush()
    }
}

pub fn main() {
    let mut args = std::env::args().collect::<Vec<_>>();

    use tracing_subscriber::{filter::EnvFilter, prelude::*};
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::layer()
                .with_writer(|| LogWriter)
                .compact()
                .without_time()
                .with_filter(EnvFilter::from_default_env()),
        )
        .with(thrust::SpanFieldsLayer.with_filter(thrust::SpanFieldsLayer::filter()))
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
