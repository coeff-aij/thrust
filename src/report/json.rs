//! The report as JSON lines, one object per site and per constraint, for a program to read.

use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

use super::constraints::{Annotation, Constraint};
use super::failure::Failure;
use super::formula::Formula;
use super::sites::{Names, Site, SiteKind};
use super::solution::{block_template, invariant, over, signature, Solution};
use super::{assumed, constraint_of, range, Entry, Items, Range};

/// One line of the report, its `kind` the variant's name.
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum Line<'a> {
    /// What the report is: its version, the directory its relative files are in, and how its
    /// columns count.
    Report {
        version: u32,
        root: String,
        columns: Columns,
    },
    /// The crate's verdict, and how many obligations a failure is refuted at: one per query, or
    /// one per part.
    Verdict {
        verdict: &'a str,
        refutations: &'a str,
        /// What the solver answered when it is neither `sat` nor `unsat` (`Timeout(30s)`).
        message: Option<String>,
    },
    Part {
        id: usize,
        clauses: usize,
        functions: Vec<FnSpan>,
        verdict: &'a str,
        cached: bool,
    },
    Site {
        r#fn: &'a str,
        site: String,
        span: Range,
        over: String,
        template: String,
        preds: Vec<Pred<'a>>,
        solution: Option<Vec<String>>,
        inferred: Option<String>,
    },
    Constraint {
        id: String,
        r#fn: &'a str,
        r#loop: Option<Range>,
        span: Option<Range>,
        obligation: &'a str,
        premises: &'a [String],
        conclusion: &'a str,
    },
    Failure {
        /// The number of its part (`THRUST_SPLIT`).
        part: Option<usize>,
        constraint: String,
        r#fn: Option<&'a str>,
        span: Option<Range>,
        obligation: Option<&'a str>,
        premises: Option<&'a [String]>,
        conclusion: Option<&'a str>,
        run: Vec<Step<'a>>,
        truncated: bool,
        values: Vec<Value>,
        /// The functions whose inferred contract the run goes through.
        inferred: Vec<&'a str>,
        /// The written annotations the refuted obligation checks.
        annotation: Vec<Range>,
        /// The functions whose written `ensures` the run assumes at a call.
        assumes: Vec<FnSpan>,
    },
}

/// How a span's columns count: from `base`, in `unit`, `end_column` after the last.
#[derive(Serialize)]
struct Columns {
    base: u32,
    unit: &'static str,
    end: &'static str,
}

/// A function and a span in it.
#[derive(Serialize)]
struct FnSpan {
    r#fn: String,
    span: Range,
}

#[derive(Serialize)]
struct Value {
    name: String,
    value: String,
}

#[derive(Serialize)]
struct Pred<'a> {
    name: &'a str,
    args: &'a [Option<String>],
}

#[derive(Serialize)]
struct Step<'a> {
    depth: usize,
    fact: String,
    /// The constraint deriving the fact, with what it stands for and where.
    via: Option<String>,
    obligation: Option<&'a str>,
    span: Option<Range>,
    /// The fact's unknown and the arguments the program names, as `fact` shows them.
    pred: &'a str,
    args: Vec<Value>,
}

pub(super) struct Json<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) items: Items,
    pub(super) names: &'a Names,
    pub(super) solution: Option<Solution>,
    /// Each failure, with the number of its part (`THRUST_SPLIT`).
    pub(super) failures: Vec<(Option<usize>, Failure)>,
    pub(super) parts: &'a [super::Part],
    pub(super) verdict: &'a str,
    pub(super) message: Option<String>,
}

impl Json<'_, '_> {
    fn site<'a>(&'a self, entry: &'a Entry<'_>, site: &Site) -> Line<'a> {
        let render = |f: &dyn Fn(&Formula) -> Formula| match site.kind {
            SiteKind::Contract => signature(&entry.name, site, self.names, &f),
            _ => invariant(site, self.names, &f),
        };
        let kind = match site.kind {
            SiteKind::Contract => "contract".to_owned(),
            SiteKind::Loop(_) => "loop".to_owned(),
            SiteKind::Block(bb) => format!("{bb:?}"),
        };
        let preds = site
            .preds
            .iter()
            .filter_map(|p| self.names.preds.get(p))
            .map(|info| Pred {
                name: &info.name,
                args: &info.args,
            })
            .collect();
        let solution = self.solution.as_ref().filter(|s| s.solves(site));
        Line::Site {
            r#fn: &entry.name,
            site: kind,
            span: range(self.tcx, site.span),
            over: over(site),
            template: match site.kind {
                SiteKind::Contract => render(&Formula::clone),
                _ => block_template(site, self.names),
            },
            preds,
            solution: solution
                .filter(|_| self.items.solution)
                .map(|s| s.lines(site, self.names)),
            inferred: solution
                .filter(|_| self.items.inferred)
                .map(|s| render(&|f| s.apply(f))),
        }
    }

    fn constraint<'a>(
        &self,
        entry: &'a Entry<'_>,
        header: Option<BasicBlock>,
        c: &'a Constraint,
    ) -> Line<'a> {
        Line::Constraint {
            id: format!("{:?}", c.id),
            r#fn: &entry.name,
            r#loop: header
                .and_then(|h| entry.body.span(h, None))
                .map(|span| range(self.tcx, span)),
            span: c.span.map(|span| range(self.tcx, span)),
            obligation: &c.kind,
            premises: &c.premises,
            conclusion: &c.conclusion,
        }
    }

    fn failure<'a>(
        &self,
        entries: &'a [Entry<'_>],
        part: Option<usize>,
        failure: &'a Failure,
    ) -> Line<'a> {
        let found = constraint_of(entries, failure.goal);
        let run = failure
            .run
            .iter()
            .map(|step| {
                let via = step.via.and_then(|id| constraint_of(entries, id));
                Step {
                    depth: step.depth,
                    fact: step.fact.clone(),
                    via: step.via.map(|id| format!("{id:?}")),
                    obligation: via.map(|(_, c)| c.kind.as_str()),
                    span: via.and_then(|(_, c)| c.span).map(|s| range(self.tcx, s)),
                    pred: &step.pred,
                    args: step
                        .args
                        .iter()
                        .map(|(name, value)| Value {
                            name: name.clone(),
                            value: value.clone(),
                        })
                        .collect(),
                }
            })
            .collect();
        Line::Failure {
            part,
            constraint: format!("{:?}", failure.goal),
            r#fn: found.map(|(e, _)| e.name.as_str()),
            span: found.and_then(|(_, c)| c.span).map(|s| range(self.tcx, s)),
            obligation: found.map(|(_, c)| c.kind.as_str()),
            premises: found.map(|(_, c)| c.premises.as_slice()),
            conclusion: found.map(|(_, c)| c.conclusion.as_str()),
            run,
            truncated: failure.truncated,
            values: found
                .map(|(_, c)| failure.named_values(c))
                .unwrap_or_default()
                .into_iter()
                .map(|(name, value)| Value { name, value })
                .collect(),
            inferred: failure
                .inferred
                .iter()
                .filter_map(|def| entries.iter().find(|e| e.def == *def))
                .map(|e| e.name.as_str())
                .collect(),
            annotation: match found.map(|(_, c)| &c.annotation) {
                Some(Annotation::Checks(spans)) => {
                    spans.iter().map(|s| range(self.tcx, *s)).collect()
                }
                _ => Vec::new(),
            },
            assumes: assumed(self.tcx, entries, failure)
                .into_iter()
                .map(|(name, span)| FnSpan {
                    r#fn: name,
                    span: range(self.tcx, span),
                })
                .collect(),
        }
    }

    pub(super) fn write(
        &self,
        entries: &[Entry<'_>],
        out: &mut dyn std::io::Write,
    ) -> std::io::Result<()> {
        let mut line = |line: Line<'_>| writeln!(out, "{}", serde_json::to_string(&line)?);
        line(Line::Report {
            version: 2,
            root: std::env::current_dir()
                .unwrap_or_default()
                .display()
                .to_string(),
            columns: Columns {
                base: 1,
                unit: "char",
                end: "exclusive",
            },
        })?;
        line(Line::Verdict {
            verdict: self.verdict,
            refutations: if self.parts.is_empty() {
                "one per query"
            } else {
                "one per part"
            },
            message: self.message.clone(),
        })?;
        for part in self.parts {
            line(Line::Part {
                id: part.id,
                clauses: part.clauses,
                functions: part
                    .functions
                    .iter()
                    .map(|f| FnSpan {
                        r#fn: f.r#fn.clone(),
                        span: range(self.tcx, f.span),
                    })
                    .collect(),
                verdict: part.verdict,
                cached: part.cached,
            })?;
        }
        for (part, failure) in &self.failures {
            line(self.failure(entries, *part, failure))?;
        }
        // Without a solution, a site has only its template to show, if that was asked for.
        let shown = |site: &Site| {
            let solved = self.solution.as_ref().is_some_and(|s| s.solves(site));
            self.items.template || (solved && (self.items.solution || self.items.inferred))
        };
        for entry in entries {
            let loop_sites = entry.loops.values().filter_map(|(site, _)| site.as_ref());
            let internal = entry.blocks.iter().filter(|_| self.items.internal);
            let entry_sites = entry.contract.iter().chain(loop_sites).chain(internal);
            for site in entry_sites.filter(|site| shown(site)) {
                line(self.site(entry, site))?;
            }
            if !self.items.constraints {
                continue;
            }
            for c in &entry.constraints {
                line(self.constraint(entry, None, c))?;
            }
            for (header, (_, constraints)) in &entry.loops {
                for c in constraints {
                    line(self.constraint(entry, Some(*header), c))?;
                }
            }
        }
        Ok(())
    }
}
