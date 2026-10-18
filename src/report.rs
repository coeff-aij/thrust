//! The report: the templates Thrust infers refinements for, the constraints it infers them from,
//! and what the solver answered, arranged by the code they come from, for a person or an agent
//! reading the program.
//!
//! It is separate from the log (`RUST_LOG`), which follows the analysis rather than the program.
//! `THRUST_REPORT` selects what it shows; see the README for the variables.
//!
//! A predicate variable belongs to the template it was made for (a function's contract or a
//! block's type, see [`sites`]); a clause belongs to the code it was made in (a function, or the
//! innermost loop around the block it was made in, see [`constraints`]). So each function and
//! each loop gets one entry, with its template and the constraints its code contributes, and the
//! entries refer to one another through the predicate variables' names.

mod body;
mod constraints;
mod failure;
mod formula;
mod human;
mod json;
mod parts;
mod proof;
mod simplify;
mod sites;
mod solution;

use std::collections::{BTreeMap, HashMap};

use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::Span;

use crate::analyze::selection::Selection;
use crate::analyze::ContractAnnotations;
use crate::chc;
use crate::refine::BasicBlockType;
use crate::rty;

use body::DefBody;
use constraints::Constraint;
use human::Human;
use json::Json;
use sites::{Names, Site, SiteKind};
use solution::Solution;

pub use parts::{emit_notes as emit_part_notes, Part};

#[derive(Debug, Clone, Copy, Default)]
struct Items {
    template: bool,
    constraints: bool,
    solution: bool,
    inferred: bool,
    failure: bool,
    internal: bool,
}

impl Items {
    const ALL: Items = Items {
        template: true,
        constraints: true,
        solution: true,
        inferred: true,
        failure: true,
        internal: true,
    };

    /// What `THRUST_REPORT=1` shows, to a person and to a program: what was inferred and why
    /// verification failed.
    const DEFAULT: Items = Items {
        template: false,
        constraints: false,
        solution: false,
        inferred: true,
        failure: true,
        internal: false,
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Format {
    Human,
    Json,
}

/// What `THRUST_REPORT`, `THRUST_REPORT_FORMAT`, `THRUST_REPORT_FILE` and `THRUST_REPORT_ONLY`
/// ask for.
pub struct Config {
    items: Items,
    format: Format,
    file: Option<std::path::PathBuf>,
    only: Option<Selection>,
}

impl Config {
    /// `None` when `THRUST_REPORT` is unset or names nothing to show.
    pub fn from_env(tcx: TyCtxt<'_>) -> Option<Self> {
        let value = std::env::var("THRUST_REPORT").ok()?;
        let format = match std::env::var("THRUST_REPORT_FORMAT").as_deref() {
            Ok("json") => Format::Json,
            Ok("human") | Err(_) => Format::Human,
            Ok(other) => {
                tcx.dcx().warn(format!(
                    "`THRUST_REPORT_FORMAT`: unknown format `{other}`, using `human`"
                ));
                Format::Human
            }
        };
        let mut items = Items::default();
        for item in value.split(',').map(str::trim).filter(|i| !i.is_empty()) {
            match item {
                "1" => items = Items::DEFAULT,
                "all" => items = Items::ALL,
                "template" => items.template = true,
                "constraints" => items.constraints = true,
                "solution" => items.solution = true,
                "inferred" => items.inferred = true,
                "failure" => items.failure = true,
                "internal" => items.internal = true,
                _ => {
                    tcx.dcx()
                        .warn(format!("`THRUST_REPORT`: unknown item `{item}` ignored"));
                }
            }
        }
        if !(items.template
            || items.constraints
            || items.solution
            || items.inferred
            || items.failure)
        {
            return None;
        }
        Some(Config {
            items,
            format,
            file: std::env::var_os("THRUST_REPORT_FILE").map(Into::into),
            only: Selection::from_var("THRUST_REPORT_ONLY"),
        })
    }

    /// Whether the report shows `def`: written in the program, and among `THRUST_REPORT_ONLY`.
    pub fn reports(&self, tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
        user_written(tcx, def)
            && self
                .only
                .as_ref()
                .is_none_or(|only| only.contains(tcx, def.to_def_id()))
    }

    /// What the report needs from the solver besides the verdict.
    pub fn requests(&self) -> chc::Requests {
        chc::Requests {
            model: self.items.solution || self.items.inferred,
            proof: self.items.failure,
        }
    }
}

/// What the analysis leaves for the report.
pub struct Input<'a> {
    pub system: &'a chc::System,
    /// The contract of each function, written or a template.
    pub contracts: Vec<(LocalDefId, &'a rty::FunctionType)>,
    pub blocks: Vec<(LocalDefId, BasicBlock, &'a BasicBlockType)>,
    /// The solver's answers: one for the whole system, or with `THRUST_SPLIT` one for each part
    /// `asked` names. A solution is read from those with a model, a failure from each.
    pub answers: &'a [chc::Answer],
    pub asked: &'a [Asked],
    /// Where the analysis made each template's predicate variable.
    pub template_sites: &'a HashMap<chc::PredVarId, crate::analyze::TemplateSite>,
    /// The variable each argument of a template's predicate variable is.
    pub template_vars: &'a HashMap<chc::PredVarId, Vec<Option<chc::debug::ErasedVar>>>,
    /// Where each function's written contract is annotated.
    pub contract_annotations: &'a HashMap<DefId, ContractAnnotations>,
    /// Where the written invariant of each loop, by its function and header, is annotated.
    pub invariant_annotations: &'a HashMap<(LocalDefId, BasicBlock), Vec<Span>>,
    /// The parts of the system solved on their own (`THRUST_SPLIT`); the system is then that of
    /// the parts refuted.
    pub parts: &'a [Part],
}

/// A part of the system solved once more for the report (`THRUST_SPLIT`): for its refutation
/// when it is refuted, else for its model.
pub struct Asked {
    /// Its number among the parts, from 1.
    pub part: usize,
    pub clauses: Vec<chc::ClauseId>,
    pub refuted: bool,
}

/// One function: its sites and constraints, the loops' ones under their headers.
struct Entry<'tcx> {
    def: LocalDefId,
    name: String,
    span: Span,
    body: DefBody<'tcx>,
    contract: Option<Site>,
    constraints: Vec<Constraint>,
    loops: BTreeMap<BasicBlock, (Option<Site>, Vec<Constraint>)>,
    blocks: Vec<Site>,
}

/// The constraint of clause `id`, with the function it is in.
fn constraint_of<'a, 'tcx>(
    entries: &'a [Entry<'tcx>],
    id: chc::ClauseId,
) -> Option<(&'a Entry<'tcx>, &'a Constraint)> {
    entries.iter().find_map(|entry| {
        let in_loops = entry.loops.values().flat_map(|(_, cs)| cs);
        let c = entry
            .constraints
            .iter()
            .chain(in_loops)
            .find(|c| c.id == id)?;
        Some((entry, c))
    })
}

/// The functions whose written `ensures` the run of `failure` assumes at a call, each with the
/// first span of its annotation.
fn assumed(
    tcx: TyCtxt<'_>,
    entries: &[Entry<'_>],
    failure: &failure::Failure,
) -> Vec<(String, Span)> {
    let mut assumed: Vec<(String, Span)> = Vec::new();
    for step in &failure.run {
        let Some((_, c)) = step.via.and_then(|id| constraint_of(entries, id)) else {
            continue;
        };
        let constraints::Annotation::Assumes(callee, spans) = &c.annotation else {
            continue;
        };
        // The injected `std.rs` is no annotation of the program's.
        if in_injected_std(tcx, spans[0]) {
            continue;
        }
        let name = tcx.def_path_str(*callee);
        if assumed.iter().all(|(n, _)| *n != name) {
            assumed.push((name, spans[0]));
        }
    }
    assumed
}

/// Whether `def` is written in the program, rather than injected (`std.rs`) or expanded from a
/// macro (the companions of the annotations).
fn user_written(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    use rustc_span::hygiene::{ExpnKind, MacroKind};
    let span = tcx.def_span(def.to_def_id());
    // A function an annotation (an attribute macro) emits again is the one written; a derive or
    // another macro writes its own.
    let written = !span.from_expansion()
        || matches!(
            span.ctxt().outer_expn_data().kind,
            ExpnKind::Macro(MacroKind::Attr, _)
        );
    written && !in_injected_std(tcx, span)
}

/// The file of `span`, relative to the working directory when it is under it.
fn file_name(tcx: TyCtxt<'_>, span: Span) -> String {
    let file = tcx.sess.source_map().lookup_char_pos(span.lo()).file;
    let name = file.name.prefer_local().to_string();
    let cwd = std::env::current_dir().unwrap_or_default();
    std::path::Path::new(&name)
        .strip_prefix(&cwd)
        .map(|relative| relative.display().to_string())
        .unwrap_or(name)
}

/// Where a span starts and ends, as JSON writes it.
#[derive(serde::Serialize)]
struct Range {
    file: String,
    line: usize,
    column: usize,
    end_line: usize,
    end_column: usize,
}

/// The range of `span`, its columns counted from 1 in characters, `end_column` after the last.
fn range(tcx: TyCtxt<'_>, span: Span) -> Range {
    let source_map = tcx.sess.source_map();
    let (lo, hi) = (
        source_map.lookup_char_pos(span.lo()),
        source_map.lookup_char_pos(span.hi()),
    );
    Range {
        file: file_name(tcx, span),
        line: lo.line,
        column: lo.col.0 + 1,
        end_line: hi.line,
        end_column: hi.col.0 + 1,
    }
}

/// Whether `span` is in the injected `std.rs`.
fn in_injected_std(tcx: TyCtxt<'_>, span: Span) -> bool {
    matches!(
        tcx.sess.source_map().span_to_filename(span),
        rustc_span::FileName::Custom(name) if name == crate::INJECTED_STD_FILE_NAME
    )
}

/// `file:line:column` of `span`.
fn location(tcx: TyCtxt<'_>, span: Span) -> String {
    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
    format!("{}:{}:{}", file_name(tcx, span), loc.line, loc.col.0 + 1)
}

/// Puts each clause, as a constraint, in the entry of the code it was made in, in place of those
/// there.
fn add_constraints(
    tcx: TyCtxt<'_>,
    input: &Input<'_>,
    names: &Names,
    entries: &mut HashMap<LocalDefId, Entry<'_>>,
) {
    for entry in entries.values_mut() {
        entry.constraints.clear();
        for (_, constraints) in entry.loops.values_mut() {
            constraints.clear();
        }
    }
    for (id, clause) in input.system.clauses.iter_enumerated() {
        let provenance = constraints::Provenance::of(&clause.debug_info);
        let Some(entry) = provenance.def.and_then(|def| entries.get_mut(&def)) else {
            continue;
        };
        let constraint = constraints::constraint(tcx, id, clause, names, Some(&entry.body), input);
        match provenance.bb.and_then(|bb| entry.body.innermost_loop(bb)) {
            Some(header) => entry.loops.entry(header).or_default().1.push(constraint),
            None => entry.constraints.push(constraint),
        }
    }
}

fn entries<'tcx>(
    tcx: TyCtxt<'tcx>,
    config: &Config,
    input: &Input<'_>,
) -> (Vec<Entry<'tcx>>, Names) {
    let selected = |def: LocalDefId| config.reports(tcx, def);
    let mut entries: HashMap<LocalDefId, Entry<'tcx>> = HashMap::new();
    for (def, _, _) in &input.blocks {
        if entries.contains_key(def) || !selected(*def) {
            continue;
        }
        let entry = Entry {
            def: *def,
            name: tcx.def_path_str(def.to_def_id()),
            span: tcx.def_span(def.to_def_id()).source_callsite(),
            body: DefBody::new(tcx, *def),
            contract: None,
            constraints: Vec::new(),
            loops: BTreeMap::new(),
            blocks: Vec::new(),
        };
        entries.insert(*def, entry);
    }

    let mut names = Names::new(input.system, input.template_sites, input.template_vars);
    for (def, fn_ty) in &input.contracts {
        let Some(entry) = entries.get_mut(def) else {
            continue;
        };
        if entry.contract.is_none() {
            entry.contract = sites::contract_site(
                &mut names,
                &entry.name,
                *def,
                &entry.body,
                entry.span,
                fn_ty,
            );
        }
    }
    let mut blocks = input.blocks.clone();
    blocks.sort_by_key(|(def, bb, _)| (def.local_def_index, *bb));
    for (def, bb, ty) in &blocks {
        let Some(entry) = entries.get_mut(def) else {
            continue;
        };
        let Some(site) = sites::block_site(&mut names, &entry.name, *def, &entry.body, *bb, ty)
        else {
            continue;
        };
        match site.kind {
            SiteKind::Loop(header) => {
                let slot = &mut entry.loops.entry(header).or_default().0;
                slot.get_or_insert(site);
            }
            _ if entry.blocks.iter().all(|b| b.kind != site.kind) => entry.blocks.push(site),
            _ => {}
        }
    }
    names.name_calls(
        |def, bb| {
            let body = &entries.get(&def)?.body;
            let rustc_middle::mir::TerminatorKind::Call { destination, .. } =
                &body.terminator(bb)?.kind
            else {
                return None;
            };
            let (callee, n) = body.call(bb)?;
            Some(sites::CallAt {
                name: format!("{}.{callee}#{n}", entries[&def].name),
                result: body.local_name(destination.local),
                arguments: body.call_args(bb).into_iter().flatten().collect(),
            })
        },
        |def, bb| Some(format!("{}.{bb:?}", entries.get(&def)?.name)),
        |def, path| entries[&def].body.path_name(path),
    );
    add_constraints(tcx, input, &names, &mut entries);

    let mut entries: Vec<_> = entries.into_values().collect();
    entries.sort_by_key(|e| (e.span.lo(), e.def.local_def_index));
    (entries, names)
}

/// How the report shows the refutation of an answer.
#[derive(Debug, Clone, Copy)]
pub enum Refuted {
    /// Not at all: the verification error is without it.
    No,
    /// At a span, where the verification error goes.
    At(Span),
    /// As the verification error itself, which the report emitted.
    AsError,
}

/// Reports `input`, and returns how it shows the refutation of each answer.
pub fn emit(tcx: TyCtxt<'_>, config: &Config, input: &Input<'_>) -> Vec<Refuted> {
    // The clauses are read as the solver is given them, a `Box` being its content.
    let system = chc::unbox(input.system.clone());
    let input = Input {
        system: &system,
        contracts: input.contracts.clone(),
        blocks: input.blocks.clone(),
        answers: input.answers,
        asked: input.asked,
        template_sites: input.template_sites,
        template_vars: input.template_vars,
        contract_annotations: input.contract_annotations,
        invariant_annotations: input.invariant_annotations,
        parts: input.parts,
    };
    // An answer is over the symbols of the query it answers: the whole system's, or a part's,
    // which numbers its own sorts.
    let capabilities = chc::Config::from_env().capabilities();
    let symbols: Vec<chc::answer::Symbols> = (0..input.answers.len())
        .map(|i| match input.asked.get(i) {
            Some(asked) => {
                chc::answer::Symbols::of(&chc::unbox(system.part(&asked.clauses)), capabilities)
            }
            None => chc::answer::Symbols::of(&system, capabilities),
        })
        .collect();
    let (entries, names) = entries(tcx, config, &input);
    let split = !input.parts.is_empty();
    let solution = Solution::of_parts(input.answers, input.asked, &system, &symbols, &names);
    let verdict = if split {
        let verdicts: Vec<&'static str> = input.parts.iter().map(|p| p.verdict).collect();
        parts::crate_verdict(&verdicts)
    } else {
        chc::verdict(&input.answers[0].result)
    };
    let failures: Vec<(&chc::Answer, Option<failure::Failure>)> = input
        .answers
        .iter()
        .zip(&symbols)
        .filter(|_| config.items.failure)
        .map(|(answer, symbols)| (answer, failure::read(answer, &names, symbols)))
        .collect();
    let refuted_at: Vec<Option<Span>> = (0..input.answers.len())
        .map(|i| {
            let (_, failure) = failures.get(i)?;
            let (_, c) = constraint_of(&entries, failure.as_ref()?.goal)?;
            c.error_span
        })
        .collect();
    // A person reads the refutation as the error; a program, the error at its span.
    let refuted: Vec<Refuted> = refuted_at
        .iter()
        .map(|span| match (span, config.format) {
            (None, _) => Refuted::No,
            (Some(_), Format::Human) => Refuted::AsError,
            (Some(span), Format::Json) => Refuted::At(*span),
        })
        .collect();
    match config.format {
        Format::Human => {
            let human = Human {
                tcx,
                items: config.items,
                names: &names,
                solution,
                split,
            };
            for (i, (answer, failure)) in failures.iter().enumerate() {
                let asked = input.asked.get(i);
                let part_note = asked.map(|a| input.parts[a.part - 1].error_note(tcx, input.parts));
                human.failure(answer, asked, part_note, failure.as_ref(), &entries);
            }
            human.emit(&entries);
        }
        Format::Json => {
            let json = Json {
                tcx,
                items: config.items,
                names: &names,
                solution: solution.ok(),
                failures: failures
                    .into_iter()
                    .enumerate()
                    .filter_map(|(i, (_, f))| Some((input.asked.get(i).map(|a| a.part), f?)))
                    .collect(),
                parts: input.parts,
                verdict,
                // A whole query without an answer is at the code of its clauses, as a part is.
                functions: (!split && !matches!(verdict, "sat" | "unsat")).then(|| {
                    let ids: Vec<chc::ClauseId> = system.clauses.indices().collect();
                    parts::code(tcx, &system, &ids)
                }),
                // With parts, that of the first part with the crate's verdict.
                message: if split {
                    let first = input.parts.iter().find(|p| p.verdict == verdict);
                    first.and_then(|p| Some(format!("part {}: {}", p.id, p.message.as_ref()?)))
                } else {
                    parts::message(&input.answers[0].result)
                },
            };
            let result = match &config.file {
                Some(path) => {
                    std::fs::File::create(path).and_then(|mut f| json.write(&entries, &mut f))
                }
                None => json.write(&entries, &mut std::io::stdout().lock()),
            };
            if let Err(err) = result {
                tcx.dcx().err(format!("could not write the report: {err}"));
            }
        }
    }
    refuted
}
