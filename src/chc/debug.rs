//! Attachable debug information for CHC clauses.
//!
//! The [`DebugInfo`] struct captures contextual information (like `tracing` spans) at the time
//! of a clause's creation. This information is then pretty-printed as comments in the
//! generated SMT-LIB2 file, which helps in tracing a clause back to its origin in the
//! Thrust codebase.

pub mod origin;

use rustc_middle::mir::{self, BasicBlock};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefIndex, LocalDefId};
use rustc_span::Span;

/// A variable of the analysis kept with its type erased, for the code that knows the type to
/// read back (the report): what an argument of a template or an entry of a clause's typing
/// environment was made for.
#[derive(Clone)]
pub struct ErasedVar(std::sync::Arc<dyn std::any::Any + Send + Sync>);

impl ErasedVar {
    pub fn new<T: std::any::Any + Send + Sync>(var: T) -> Self {
        ErasedVar(std::sync::Arc::new(var))
    }

    pub fn downcast_ref<T: std::any::Any>(&self) -> Option<&T> {
        self.0.downcast_ref()
    }
}

impl std::fmt::Debug for ErasedVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ErasedVar")
    }
}

#[derive(Debug, Clone)]
pub struct Display<'a> {
    inner: &'a DebugInfo,
    line_head: &'static str,
}

impl<'a> std::fmt::Display for Display<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.line_head)?;
        for (key, value) in &self.inner.contexts {
            let mut lines = value.lines();
            write!(f, "{}={}", key, lines.next().unwrap_or_default())?;
            for line in lines {
                write!(f, "\n{}{}", self.line_head, line)?;
            }
            write!(f, " ")?;
        }
        Ok(())
    }
}

/// The fields that place a clause or a declaration in the source: the span it was made in, the
/// definition, basic block, statement and terminator, and the type parameter of a forall sort.
const ORIGIN_KEYS: [&str; 7] = [
    "span",
    "def",
    "def_id",
    "bb",
    "stmt_idx",
    "term",
    "type_param",
];

/// The [`ORIGIN_KEYS`] fields of a [`DebugInfo`] on one line, each preceded by a space.
#[derive(Debug, Clone)]
pub struct OriginLine<'a> {
    inner: &'a DebugInfo,
}

impl std::fmt::Display for OriginLine<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (key, value) in &self.inner.contexts {
            if !ORIGIN_KEYS.contains(&key.as_str()) {
                continue;
            }
            write!(f, " {key}=")?;
            for (i, line) in value.lines().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{line}")?;
            }
        }
        Ok(())
    }
}

/// A purely informational metadata that can be attached to a clause.
#[derive(Debug, Clone, Default)]
pub struct DebugInfo {
    contexts: Vec<(String, String)>,
    /// The fields recorded as numbers, as the analysis gave them (a def's index, a block's), in
    /// the order of `contexts`.
    numbers: Vec<(String, u64)>,
}

/// The fields of a span, in the order they were recorded, each also as a number when it was
/// recorded as one.
#[derive(Debug, Default)]
struct SpanFields(Vec<(String, String, Option<u64>)>);

impl tracing::field::Visit for SpanFields {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn std::fmt::Debug) {
        self.0
            .push((field.name().to_owned(), format!("{value:?}"), None));
    }

    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        self.0
            .push((field.name().to_owned(), value.to_string(), Some(value)));
    }
}

/// Keeps the fields of every span it sees in the span's extensions, so that
/// [`DebugInfo::from_current_span`] reads them as recorded rather than from a formatted log
/// line. It records the spans [`SpanFieldsLayer::filter`] enables.
pub struct SpanFieldsLayer;

impl SpanFieldsLayer {
    /// Thrust's spans at `info` and above, whatever `RUST_LOG` says, since they place each clause
    /// and declaration in the source for the report (`crate::report`) as well as for the comments
    /// of the query; and every span the log output enables, so that a span is recorded whenever
    /// it is logged.
    pub fn filter<S>() -> impl tracing_subscriber::layer::Filter<S>
    where
        S: tracing::Subscriber + for<'a> tracing_subscriber::registry::LookupSpan<'a>,
    {
        use tracing_subscriber::filter::{filter_fn, EnvFilter, FilterExt as _, LevelFilter};
        filter_fn(|meta| {
            meta.is_span()
                && meta.target().starts_with("thrust")
                && *meta.level() <= tracing::Level::INFO
        })
        .with_max_level_hint(LevelFilter::INFO)
        .or(EnvFilter::from_default_env())
    }
}

impl<S> tracing_subscriber::Layer<S> for SpanFieldsLayer
where
    S: tracing::Subscriber + for<'a> tracing_subscriber::registry::LookupSpan<'a>,
{
    fn on_new_span(
        &self,
        attrs: &tracing::span::Attributes<'_>,
        id: &tracing::span::Id,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let Some(span) = ctx.span(id) else {
            return;
        };
        let mut fields = SpanFields::default();
        attrs.record(&mut fields);
        span.extensions_mut().insert(fields);
    }

    fn on_record(
        &self,
        id: &tracing::span::Id,
        values: &tracing::span::Record<'_>,
        ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
        let Some(span) = ctx.span(id) else {
            return;
        };
        let mut extensions = span.extensions_mut();
        if let Some(fields) = extensions.get_mut::<SpanFields>() {
            values.record(fields);
        }
    }
}

impl DebugInfo {
    pub fn from_current_span() -> Self {
        let mut debug_info = Self::default();
        debug_info.context_from_current_span();
        debug_info
    }

    /// The name of the current span, then the fields of each span from the current one
    /// outwards, the fields of one span latest first.
    pub fn context_from_current_span(&mut self) {
        tracing::dispatcher::get_default(|d| {
            let current_span = d.current_span();
            if let Some(metadata) = current_span.metadata() {
                self.context("span", metadata.name());
            }
            let Some(registry) = d.downcast_ref::<tracing_subscriber::Registry>() else {
                return;
            };
            use tracing_subscriber::registry::{LookupSpan, SpanData};
            let mut span_id = current_span.id().cloned();
            while let Some(id) = span_id {
                let Some(data) = registry.span_data(&id) else {
                    break;
                };
                if let Some(fields) = data.extensions().get::<SpanFields>() {
                    for (key, value, number) in fields.0.iter().rev() {
                        self.context(key, value.clone());
                        if let Some(number) = number {
                            self.numbers.push((key.clone(), *number));
                        }
                    }
                }
                span_id = data.parent().cloned();
            }
        });
    }

    pub fn is_empty(&self) -> bool {
        self.contexts.is_empty()
    }

    /// The number recorded as the field `key` of the innermost span that has one.
    pub fn number(&self, key: &str) -> Option<u64> {
        self.numbers.iter().find(|(k, _)| k == key).map(|(_, n)| *n)
    }

    /// The value of the field `key` of the innermost span that has one.
    pub fn get(&self, key: &str) -> Option<&str> {
        self.contexts
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }

    pub fn context(&mut self, key: &str, value: impl Into<String>) -> &mut Self {
        self.contexts.push((key.to_owned(), value.into()));
        self
    }

    pub fn with_context(mut self, key: &str, value: impl Into<String>) -> Self {
        self.contexts.push((key.to_owned(), value.into()));
        self
    }

    pub fn display(&self, line_head: &'static str) -> Display<'_> {
        Display {
            inner: self,
            line_head,
        }
    }

    pub fn origin_line(&self) -> OriginLine<'_> {
        OriginLine { inner: self }
    }
}

/// Where a clause was made, read from the spans it was made in (see
/// [`SpanFieldsLayer`]).
#[derive(Debug, Clone, Copy, Default)]
pub struct Provenance {
    pub def: Option<LocalDefId>,
    pub bb: Option<BasicBlock>,
    pub stmt: Option<usize>,
}

impl Provenance {
    pub fn of(debug_info: &DebugInfo) -> Self {
        let def = debug_info.number("def_index").map(|i| LocalDefId {
            local_def_index: DefIndex::from_u32(i as u32),
        });
        let bb = debug_info
            .number("bb_index")
            .map(|i| BasicBlock::from_u32(i as u32));
        let stmt = debug_info.number("stmt_idx").map(|i| i as usize);
        Provenance { def, bb, stmt }
    }

    /// The span of the code the clause was made at: its statement or terminator (a return's,
    /// empty after the closing brace, widened over the brace), or else its function's signature.
    pub fn span(&self, tcx: TyCtxt<'_>) -> Option<Span> {
        let def = self.def?.to_def_id();
        let body = tcx.is_mir_available(def).then(|| tcx.optimized_mir(def));
        let in_body = body.zip(self.bb).and_then(|(body, bb)| {
            let span = span_in(body, bb, self.stmt)?;
            if !span.is_empty() {
                return Some(span);
            }
            if !self.at_return(body) {
                return None;
            }
            let brace = span.with_lo(rustc_span::BytePos(span.lo().0.checked_sub(1)?));
            let snippet = tcx.sess.source_map().span_to_snippet(brace).ok()?;
            (snippet == "}").then_some(brace)
        });
        Some(in_body.unwrap_or_else(|| tcx.def_span(def).source_callsite()))
    }

    /// Whether the clause was made at a return: the terminator of its block, not a statement.
    pub fn at_return(&self, body: &mir::Body<'_>) -> bool {
        let terminator = self
            .bb
            .filter(|_| self.stmt.is_none())
            .and_then(|bb| body.basic_blocks.get(bb)?.terminator.as_ref());
        matches!(
            terminator.map(|t| &t.kind),
            Some(mir::TerminatorKind::Return)
        )
    }
}

/// The span of statement `stmt` of `bb` of `body`, or of its terminator, as the user wrote it (the
/// call site of a macro such as `assert!`).
pub fn span_in(body: &mir::Body<'_>, bb: BasicBlock, stmt: Option<usize>) -> Option<Span> {
    let data = body.basic_blocks.get(bb)?;
    let span = match stmt {
        Some(idx) if idx < data.statements.len() => data.statements[idx].source_info.span,
        _ => data.terminator.as_ref()?.source_info.span,
    };
    Some(span.source_callsite())
}
