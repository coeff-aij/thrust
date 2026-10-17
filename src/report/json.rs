//! The report as JSON lines, one object per site and per constraint, for a program to read.

use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;

use super::constraints::{Annotation, Constraint};
use super::failure::Failure;
use super::formula::Formula;
use super::sites::{Names, Site, SiteKind};
use super::solution::{block_template, invariant, over, signature, Solution};
use super::{assumed, constraint_of, location, Entry, Items};

/// One line of the report, its `kind` the variant's name.
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum Line<'a> {
    Part {
        functions: &'a [String],
        verdict: &'a str,
        cached: bool,
    },
    Site {
        r#fn: &'a str,
        site: String,
        span: String,
        over: String,
        template: String,
        preds: Vec<Pred<'a>>,
        solution: Option<Vec<String>>,
        inferred: Option<String>,
    },
    Constraint {
        id: String,
        r#fn: &'a str,
        r#loop: Option<String>,
        span: Option<String>,
        obligation: &'a str,
        premises: &'a [String],
        conclusion: &'a str,
    },
    Failure {
        constraint: String,
        r#fn: Option<&'a str>,
        span: Option<String>,
        obligation: Option<&'a str>,
        premises: Option<&'a [String]>,
        conclusion: Option<&'a str>,
        run: Vec<Step>,
        truncated: bool,
        values: Vec<Value>,
        /// The functions whose inferred contract the run goes through.
        inferred: Vec<&'a str>,
        /// The written annotations the refuted obligation checks.
        annotation: Vec<String>,
        /// The functions whose written `ensures` the run assumes at a call.
        assumes: Vec<Annotated>,
    },
}

#[derive(Serialize)]
struct Annotated {
    r#fn: String,
    span: String,
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
struct Step {
    depth: usize,
    fact: String,
    via: Option<String>,
}

pub(super) struct Json<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) items: Items,
    pub(super) names: &'a Names,
    pub(super) solution: Option<Solution>,
    pub(super) failures: Vec<Failure>,
    pub(super) parts: &'a [super::Part],
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
        let solution = self.solution.as_ref();
        Line::Site {
            r#fn: &entry.name,
            site: kind,
            span: location(self.tcx, site.span),
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
                .map(|span| location(self.tcx, span)),
            span: c.span.map(|span| location(self.tcx, span)),
            obligation: &c.kind,
            premises: &c.premises,
            conclusion: &c.conclusion,
        }
    }

    fn failure<'a>(&self, entries: &'a [Entry<'_>], failure: &Failure) -> Line<'a> {
        let found = constraint_of(entries, failure.goal);
        let run = failure
            .run
            .iter()
            .map(|step| Step {
                depth: step.depth,
                fact: step.fact.clone(),
                via: step.via.map(|id| format!("{id:?}")),
            })
            .collect();
        Line::Failure {
            constraint: format!("{:?}", failure.goal),
            r#fn: found.map(|(e, _)| e.name.as_str()),
            span: found
                .and_then(|(_, c)| c.span)
                .map(|s| location(self.tcx, s)),
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
                    spans.iter().map(|s| location(self.tcx, *s)).collect()
                }
                _ => Vec::new(),
            },
            assumes: assumed(self.tcx, entries, failure)
                .into_iter()
                .map(|(name, span)| Annotated {
                    r#fn: name,
                    span: location(self.tcx, span),
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
        for part in self.parts {
            line(Line::Part {
                functions: &part.functions,
                verdict: part.verdict,
                cached: part.cached,
            })?;
        }
        for failure in &self.failures {
            line(self.failure(entries, failure))?;
        }
        for entry in entries {
            let loop_sites = entry.loops.values().filter_map(|(site, _)| site.as_ref());
            let internal = entry.blocks.iter().filter(|_| self.items.internal);
            for site in entry.contract.iter().chain(loop_sites).chain(internal) {
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
