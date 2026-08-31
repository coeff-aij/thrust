//! Attachable debug information for CHC clauses.
//!
//! The [`DebugInfo`] struct captures contextual information (like `tracing` spans) at the time
//! of a clause's creation. This information is then pretty-printed as comments in the
//! generated SMT-LIB2 file, which helps in tracing a clause back to its origin in the
//! Thrust codebase.

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

/// A purely informational metadata that can be attached to a clause.
#[derive(Debug, Clone, Default)]
pub struct DebugInfo {
    contexts: Vec<(String, String)>,
}

fn strip_ansi_colors(s: &str) -> String {
    let mut line = s.to_owned();
    let mut start = None;
    let mut offset = 0;
    for (i, b) in s.bytes().enumerate() {
        if b == b'\x1b' {
            start = Some(i);
        }
        if let Some(start_idx) = start {
            if b == b'm' {
                line.drain((start_idx - offset)..=(i - offset));
                offset += i - start_idx + 1;
                start = None;
            }
        }
    }
    line
}

impl DebugInfo {
    pub fn from_current_span() -> Self {
        let mut debug_info = Self::default();
        debug_info.context_from_current_span();
        debug_info
    }

    pub fn context_from_current_span(&mut self) {
        // XXX: hack
        tracing::dispatcher::get_default(|d| {
            let current_span = d.current_span();
            if let Some(metadata) = current_span.metadata() {
                self.context("span", metadata.name());
            }
            let Some(registry) = d.downcast_ref::<tracing_subscriber::Registry>() else {
                return;
            };
            use tracing_subscriber::registry::{LookupSpan, SpanData};
            type Extension = tracing_subscriber::fmt::FormattedFields<
                tracing_subscriber::fmt::format::DefaultFields,
            >;
            let mut span_id = current_span.id().cloned();
            while let Some(id) = span_id {
                let Some(data) = registry.span_data(&id) else {
                    break;
                };
                let exts = data.extensions();
                if let Some(fields) = exts.get::<Extension>() {
                    self.context_from_formatted_fields(&fields.fields);
                }
                span_id = data.parent().cloned();
            }
        });
    }

    fn context_from_formatted_fields(&mut self, fields: &str) {
        // `tracing_subscriber::fmt` renders span fields as `key=value` pairs. When ANSI colors
        // are enabled the `=` is dim-styled (`\x1b[2m=\x1b[0m`), which unambiguously separates
        // the key from the value even when a value contains spaces. When colors are disabled
        // (e.g. `NO_COLOR`), the pairs are plain `key=value` tokens separated by whitespace.
        // Handle both layouts, but keep only fields that are useful for tracing a clause back
        // to its function and MIR basic block. Other fields (e.g. auto-captured arguments
        // whose debug output contains spaces) would be corrupted by the plain layout parse.
        const DIM_EQ: &str = "\x1b[2m=\x1b[0m";
        let mut context = |key: &str, value: String| {
            // When a function's body is analyzed from within another function (e.g. deferred
            // calls and closures), several ancestor spans carry `def`/`bb`. The innermost one
            // is the function the clause actually belongs to, so keep only the first.
            if matches!(key, "def" | "def_id" | "bb")
                && !self.contexts.iter().any(|(k, _)| k == key)
            {
                self.context(key, value);
            }
        };
        if fields.contains(DIM_EQ) {
            let mut value: Option<String> = None;
            for field in fields.rsplit(DIM_EQ) {
                let field = strip_ansi_colors(field);
                if let Some(prev_value) = value {
                    if let Some((next_value, key)) = field.rsplit_once(' ') {
                        context(key, prev_value.to_owned());
                        value = Some(next_value.to_owned());
                    } else {
                        context(&field, prev_value.to_owned());
                        break;
                    }
                } else {
                    value = Some(field);
                    continue;
                }
            }
        } else {
            for field in fields.split_ascii_whitespace() {
                if let Some((key, value)) = field.split_once('=') {
                    context(key, value.to_owned());
                }
            }
        }
    }

    pub fn is_empty(&self) -> bool {
        self.contexts.is_empty()
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
}
