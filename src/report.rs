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
mod expr;
mod failure;
mod human;
mod json;
mod model;
mod proof;
mod simplify;
mod sites;
mod solution;

use std::collections::{BTreeMap, HashMap};

use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

use crate::analyze::selection::Selection;
use crate::chc;
use crate::refine::BasicBlockType;
use crate::rty;

use body::DefBody;
use constraints::Constraint;
use expr::Expr;
use human::Human;
use json::Json;
use sites::{Names, Site, SiteKind};
use solution::{solution_unavailable, Solution};

#[derive(Debug, Clone, Copy, Default)]
struct Items {
    template: bool,
    constraints: bool,
    solution: bool,
    inferred: bool,
    failure: bool,
    internal: bool,
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
        let mut items = Items::default();
        for item in value.split(',').map(str::trim).filter(|i| !i.is_empty()) {
            match item {
                "all" => {
                    items = Items {
                        template: true,
                        constraints: true,
                        solution: true,
                        inferred: true,
                        failure: true,
                        internal: true,
                    }
                }
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
        Some(Config {
            items,
            format,
            file: std::env::var_os("THRUST_REPORT_FILE").map(Into::into),
            only: Selection::from_var("THRUST_REPORT_ONLY"),
        })
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
    pub answer: &'a chc::Answer,
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

/// Whether `def` is written in the program, rather than injected (`std.rs`) or expanded from a
/// macro (the companions of the annotations).
fn user_written(tcx: TyCtxt<'_>, def: LocalDefId) -> bool {
    let span = tcx.def_span(def.to_def_id());
    if span.from_expansion() {
        return false;
    }
    !matches!(
        tcx.sess.source_map().span_to_filename(span),
        rustc_span::FileName::Custom(name) if name == crate::INJECTED_STD_FILE_NAME
    )
}

fn location(tcx: TyCtxt<'_>, span: Span) -> String {
    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
    format!(
        "{}:{}:{}",
        loc.file.name.prefer_local(),
        loc.line,
        loc.col.0 + 1
    )
}

/// Puts each clause, as a constraint, in the entry of the code it was made in, in place of those
/// there.
fn add_constraints(
    tcx: TyCtxt<'_>,
    system: &chc::System,
    names: &Names,
    entries: &mut HashMap<LocalDefId, Entry<'_>>,
) {
    for entry in entries.values_mut() {
        entry.constraints.clear();
        for (_, constraints) in entry.loops.values_mut() {
            constraints.clear();
        }
    }
    for (id, clause) in system.clauses.iter_enumerated() {
        let provenance = constraints::Provenance::of(&clause.debug_info);
        let Some(entry) = provenance.def.and_then(|def| entries.get_mut(&def)) else {
            continue;
        };
        let constraint = constraints::constraint(tcx, id, clause, names, Some(&entry.body));
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
    let selected = |def: LocalDefId| {
        user_written(tcx, def)
            && config
                .only
                .as_ref()
                .is_none_or(|only| only.contains(tcx, def.to_def_id()))
    };
    let mut entries: HashMap<LocalDefId, Entry<'tcx>> = HashMap::new();
    for (def, _, _) in &input.blocks {
        if entries.contains_key(def) || !selected(*def) {
            continue;
        }
        let entry = Entry {
            def: *def,
            name: tcx.def_path_str(def.to_def_id()),
            span: tcx.def_span(def.to_def_id()),
            body: DefBody::new(tcx, *def),
            contract: None,
            constraints: Vec::new(),
            loops: BTreeMap::new(),
            blocks: Vec::new(),
        };
        entries.insert(*def, entry);
    }

    let mut names = Names::new(input.system);
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
    // The rest are made for the result of a call, the first argument standing for the result:
    // `f.g#2` for the result of the second call to `g` in `f`.
    names.name_rest(|def, bb| {
        let entry = entries.get(&def)?;
        let bb = bb?;
        let rustc_middle::mir::TerminatorKind::Call { destination, .. } =
            &entry.body.terminator(bb)?.kind
        else {
            return Some((format!("{}.{bb:?}", entry.name), Vec::new(), Vec::new()));
        };
        let result = Some(entry.body.local_name(destination.local));
        let name = match entry.body.call(bb) {
            Some((callee, n)) => format!("{}.{callee}#{n}", entry.name),
            None => format!("{}.{bb:?}", entry.name),
        };
        Some((name, vec![result], vec![1]))
    });

    // A call's result has no template naming the variables it depends on; the constraint that
    // defines it, made at the call, names them, and among them the call's arguments are shown
    // apart from the other variables. The constraints are then shown with those names.
    add_constraints(tcx, input.system, &names, &mut entries);
    for entry in entries.values() {
        let in_loops = entry.loops.values().flat_map(|(_, cs)| cs);
        for c in entry.constraints.iter().chain(in_loops) {
            if let Expr::Pred(name, groups, args) = &c.conclusion {
                if !groups.is_empty() {
                    names.name_args_after(name, args);
                }
            }
        }
    }
    for (p, def, bb) in names.call_results() {
        let Some(entry) = entries.get(&def) else {
            continue;
        };
        let call_args: Vec<String> = entry
            .body
            .call_args(bb)
            .into_iter()
            .flatten()
            .map(|local| entry.body.local_name(local))
            .collect();
        names.group_call_args(p, &call_args);
    }
    add_constraints(tcx, input.system, &names, &mut entries);

    let mut entries: Vec<_> = entries.into_values().collect();
    entries.sort_by_key(|e| (e.span.lo(), e.def.local_def_index));
    (entries, names)
}

pub fn emit(tcx: TyCtxt<'_>, config: &Config, input: &Input<'_>) {
    // The clauses are read as the solver is given them, a `Box` being its content.
    let system = chc::unbox(input.system.clone());
    let input = Input {
        system: &system,
        contracts: input.contracts.clone(),
        blocks: input.blocks.clone(),
        answer: input.answer,
    };
    let (entries, names) = entries(tcx, config, &input);
    let solution = match (solution_unavailable(input.answer), &input.answer.model) {
        (None, Some(model)) => {
            let config = chc::Config::from_env();
            let query = input.answer.query.as_deref().unwrap_or_default();
            Ok(Solution::new(model, query, &names, |script| {
                config.run_script(script)
            }))
        }
        (why, _) => Err(why.unwrap_or_else(|| "no solution".to_owned())),
    };
    let failure = config
        .items
        .failure
        .then(|| failure::read(input.answer, &system, &names))
        .flatten();
    match config.format {
        Format::Human => {
            let human = Human {
                tcx,
                items: config.items,
                names: &names,
                solution,
            };
            human.failure(input.answer, failure.as_ref(), &entries);
            human.emit(&entries);
        }
        Format::Json => {
            let json = Json {
                tcx,
                items: config.items,
                names: &names,
                solution: solution.ok(),
                failure,
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
}
