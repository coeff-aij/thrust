//! The report as JSON lines, one object per site and per constraint, for a program to read.

use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;

use super::constraints::Constraint;
use super::expr::Expr;
use super::failure::Failure;
use super::sites::{Names, Site, SiteKind};
use super::solution::{invariant, over, signature, Solution};
use super::{constraint_of, location, Entry, Items};

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn json_opt(s: Option<String>) -> String {
    s.map_or_else(|| "null".to_owned(), |s| json_str(&s))
}

fn json_list(items: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", items.into_iter().collect::<Vec<_>>().join(","))
}

fn json_object(fields: &[(&str, String)]) -> String {
    let fields: Vec<_> = fields
        .iter()
        .map(|(k, v)| format!("{}:{v}", json_str(k)))
        .collect();
    format!("{{{}}}", fields.join(","))
}

pub(super) struct Json<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) items: Items,
    pub(super) names: &'a Names,
    pub(super) solution: Option<Solution>,
    pub(super) failure: Option<Failure>,
}

impl Json<'_, '_> {
    fn site(&self, entry: &Entry<'_>, site: &Site) -> String {
        let id = |e: &Expr| e.clone();
        let render = |f: &dyn Fn(&Expr) -> Expr| match site.kind {
            SiteKind::Contract => signature(&entry.name, site, &f),
            _ => invariant(site, &f).to_string(),
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
            .map(|info| {
                let args = info.args.iter().map(|a| json_opt(a.clone()));
                json_object(&[("name", json_str(&info.name)), ("args", json_list(args))])
            });
        let solution = self
            .solution
            .as_ref()
            .filter(|_| self.items.solution)
            .map(|s| json_list(s.lines(site, self.names).iter().map(|l| json_str(l))));
        let inferred = self
            .solution
            .as_ref()
            .filter(|_| self.items.inferred)
            .map(|s| render(&|e: &Expr| s.apply(e)));
        json_object(&[
            ("kind", json_str("site")),
            ("fn", json_str(&entry.name)),
            ("site", json_str(&kind)),
            ("span", json_str(&location(self.tcx, site.span))),
            ("over", json_str(&over(site))),
            ("template", json_str(&render(&id))),
            ("preds", json_list(preds)),
            ("solution", solution.unwrap_or_else(|| "null".to_owned())),
            ("inferred", json_opt(inferred)),
        ])
    }

    fn constraint(&self, entry: &Entry<'_>, header: Option<BasicBlock>, c: &Constraint) -> String {
        let loop_span = header
            .and_then(|h| entry.body.span(h, None))
            .map(|span| location(self.tcx, span));
        json_object(&[
            ("kind", json_str("constraint")),
            ("id", json_str(&format!("{:?}", c.id))),
            ("fn", json_str(&entry.name)),
            ("loop", json_opt(loop_span)),
            (
                "span",
                json_opt(c.span.map(|span| location(self.tcx, span))),
            ),
            ("obligation", json_str(&c.kind)),
            (
                "premises",
                json_list(c.premises.iter().map(|p| json_str(&p.to_string()))),
            ),
            ("conclusion", json_str(&c.conclusion.to_string())),
        ])
    }

    fn failure(&self, entries: &[Entry<'_>], failure: &Failure) -> String {
        let found = constraint_of(entries, failure.goal);
        let run = failure.run.iter().map(|step| {
            let via = step.via.map(|id| format!("{id:?}"));
            json_object(&[
                ("depth", step.depth.to_string()),
                ("fact", json_str(&step.fact)),
                ("via", json_opt(via)),
            ])
        });
        json_object(&[
            ("kind", json_str("failure")),
            ("constraint", json_str(&format!("{:?}", failure.goal))),
            ("fn", json_opt(found.map(|(e, _)| e.name.clone()))),
            (
                "span",
                json_opt(
                    found
                        .and_then(|(_, c)| c.span)
                        .map(|s| location(self.tcx, s)),
                ),
            ),
            ("obligation", json_opt(found.map(|(_, c)| c.kind.clone()))),
            ("run", json_list(run)),
            ("truncated", failure.truncated.to_string()),
        ])
    }

    pub(super) fn write(
        &self,
        entries: &[Entry<'_>],
        out: &mut dyn std::io::Write,
    ) -> std::io::Result<()> {
        if let Some(failure) = self.failure.as_ref().filter(|_| self.items.failure) {
            writeln!(out, "{}", self.failure(entries, failure))?;
        }
        for entry in entries {
            let loop_sites = entry.loops.values().filter_map(|(site, _)| site.as_ref());
            let internal = entry.blocks.iter().filter(|_| self.items.internal);
            for site in entry.contract.iter().chain(loop_sites).chain(internal) {
                writeln!(out, "{}", self.site(entry, site))?;
            }
            if !self.items.constraints {
                continue;
            }
            for c in &entry.constraints {
                writeln!(out, "{}", self.constraint(entry, None, c))?;
            }
            for (header, (_, constraints)) in &entry.loops {
                for c in constraints {
                    writeln!(out, "{}", self.constraint(entry, Some(*header), c))?;
                }
            }
        }
        Ok(())
    }
}
