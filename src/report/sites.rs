//! The places whose refinements Thrust infers, and a readable name for each predicate variable
//! they carry.
//!
//! A predicate variable belongs to the template it was made for, which the spans it was made in
//! tell: a function's contract when the function has none written, a basic block's type, or the
//! result of a call. A loop header's block type is the loop's invariant; the other blocks' types
//! are intermediate steps of the analysis.

use std::collections::HashMap;

use rustc_middle::mir::BasicBlock;
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

use crate::chc;
use crate::pretty::PrettyDisplayExt as _;
use crate::refine::{BasicBlockType, BasicBlockTypeParamKind};
use crate::rty;

use super::body::DefBody;
use super::constraints::Provenance;
use super::expr::{self, Expr, PredHead};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SiteKind {
    Contract,
    Loop(BasicBlock),
    Block(BasicBlock),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Owner {
    /// A parameter's refinement in a function's contract (`ret` for the return value's).
    Contract {
        def: LocalDefId,
        ret: bool,
    },
    Block {
        def: LocalDefId,
        bb: BasicBlock,
    },
    /// Made elsewhere in the code of `def`, such as for the result of a call.
    Other {
        def: LocalDefId,
    },
}

impl Owner {
    pub fn def(&self) -> LocalDefId {
        match *self {
            Owner::Contract { def, .. } | Owner::Block { def, .. } | Owner::Other { def } => def,
        }
    }
}

#[derive(Debug, Clone)]
pub struct PredInfo {
    pub name: String,
    /// What each argument stands for in the template, if it is a variable of the template.
    pub args: Vec<Option<String>>,
    /// How many of the first arguments are the values the template refines (the result of a
    /// call), the rest being what they may depend on.
    pub results: usize,
    /// The order the arguments are shown in, when not their own: that of the variables of the
    /// template the predicate variable is the whole of (see [`Site::signature`]).
    pub order: Option<Vec<usize>>,
    pub owner: Owner,
}

/// A parameter of a template: of a function's contract (`result` the last), or a variable a
/// block's type is over.
#[derive(Debug, Clone)]
pub struct SiteParam {
    pub name: String,
    pub ty: String,
    pub refinement: Expr,
}

#[derive(Debug, Clone)]
pub struct Site {
    pub kind: SiteKind,
    pub span: Span,
    pub params: Vec<SiteParam>,
    pub preds: Vec<chc::PredVarId>,
    /// The predicate variable that is the whole template, applied to every variable in the order
    /// of `params`, when there is one: the template is then shown as its signature,
    /// `main.loop#1(x: i64, y: i64)`.
    pub signature: Option<chc::PredVarId>,
}

/// Where each predicate variable was made.
#[derive(Debug, Clone, Copy)]
struct Made {
    def: Option<LocalDefId>,
    bb: Option<BasicBlock>,
    in_contract: bool,
}

#[derive(Debug, Default)]
pub struct Names {
    pub preds: HashMap<chc::PredVarId, PredInfo>,
    made: HashMap<chc::PredVarId, Made>,
}

impl Names {
    pub fn new(system: &chc::System) -> Self {
        let made = system
            .pred_vars
            .iter_enumerated()
            .map(|(p, def)| {
                let provenance = Provenance::of(&def.debug_info);
                let made = Made {
                    def: provenance.def,
                    bb: provenance.bb,
                    in_contract: def.debug_info.get("span") == Some("refine_fn_def"),
                };
                (p, made)
            })
            .collect();
        Names {
            preds: HashMap::new(),
            made,
        }
    }

    /// How `p` is shown.
    pub fn pred_head(&self, p: chc::PredVarId) -> PredHead {
        match self.preds.get(&p) {
            Some(info) => PredHead {
                name: info.name.clone(),
                results: info.results,
                order: info.order.clone(),
            },
            None => PredHead {
                name: p.to_string(),
                results: 0,
                order: None,
            },
        }
    }

    /// Names the arguments of the predicate variable `name` that its template leaves unnamed after
    /// `args`, its arguments in the head of a constraint of the code that made it.
    pub fn name_args_after(&mut self, name: &str, args: &[Expr]) {
        let Some(info) = self.preds.values_mut().find(|info| info.name == name) else {
            return;
        };
        if info.args.len() < args.len() {
            info.args.resize(args.len(), None);
        }
        for (slot, arg) in info.args.iter_mut().zip(args) {
            match arg {
                Expr::Sym(s) if slot.is_none() && !s.starts_with("__tmp_chc_") => {
                    *slot = Some(s.clone());
                }
                _ => {}
            }
        }
    }

    fn made_in_contract(&self, p: chc::PredVarId, def: LocalDefId) -> bool {
        self.made
            .get(&p)
            .is_some_and(|m| m.in_contract && m.def == Some(def))
    }

    fn made_in_block(&self, p: chc::PredVarId, def: LocalDefId, bb: BasicBlock) -> bool {
        self.made
            .get(&p)
            .is_some_and(|m| !m.in_contract && m.def == Some(def) && m.bb == Some(bb))
    }

    /// Names each predicate variable no template claimed after the code it was made in:
    /// `name_of(def, bb)` names one made in block `bb` of `def`, with what its arguments stand
    /// for as far as the code tells.
    pub fn name_rest(
        &mut self,
        name_of: impl Fn(LocalDefId, Option<BasicBlock>) -> Option<(String, Vec<Option<String>>, usize)>,
    ) {
        let mut rest: Vec<_> = self
            .made
            .iter()
            .filter(|(p, _)| !self.preds.contains_key(p))
            .filter_map(|(p, m)| Some((*p, m.def?, m.bb)))
            .collect();
        rest.sort_by_key(|(p, _, _)| p.index());
        let mut counts: HashMap<String, usize> = HashMap::new();
        for (p, def, bb) in rest {
            let Some((base, args, results)) = name_of(def, bb) else {
                continue;
            };
            let count = counts.entry(base.clone()).or_default();
            *count += 1;
            let name = if *count == 1 {
                base
            } else {
                format!("{base}_{count}")
            };
            let info = PredInfo {
                name,
                args,
                results,
                order: None,
                owner: Owner::Other { def },
            };
            self.preds.insert(p, info);
        }
    }
}

/// The type as the program writes it: a local the analysis holds behind an owned pointer
/// (`own T`) is a `T`.
fn rust_type(ty: &str) -> String {
    ty.strip_prefix("own ").unwrap_or(ty).to_owned()
}

/// An existential of a refinement, which Thrust introduces in typing a value.
fn existential_name(e: rty::ExistentialVarIdx) -> String {
    format!("__tmp_rty_{e}")
}

fn pred_vars<V>(
    refinement: &rty::Refinement<V>,
) -> Vec<(chc::PredVarId, &chc::Atom<rty::RefinedTypeVar<V>>)> {
    refinement
        .body
        .atoms
        .iter()
        .filter_map(|atom| match atom.pred {
            chc::Pred::Var(p) => Some((p, atom)),
            _ => None,
        })
        .collect()
}

type Param<'a> = (String, &'a rty::RefinedType<rty::FunctionParamIdx>);

fn var_name(
    params: &[Param<'_>],
    own: &str,
    v: &rty::RefinedTypeVar<rty::FunctionParamIdx>,
) -> String {
    match v {
        rty::RefinedTypeVar::Value => own.to_owned(),
        rty::RefinedTypeVar::Free(idx) => params
            .get(idx.index())
            .map(|(n, _)| n.clone())
            .unwrap_or_else(|| idx.to_string()),
        rty::RefinedTypeVar::Existential(e) => existential_name(*e),
    }
}

/// Names the predicate variables of one template that `claims` accepts, `params` being its
/// parameters by name, and returns them in order. `name_of(k, n, own)` is the name of the `k`-th
/// of the `n` variables found, in the refinement of the parameter named `own`; `owner_of(i)` is
/// the owner of those in parameter `i`.
fn name_preds(
    names: &mut Names,
    params: &[Param<'_>],
    claims: impl Fn(&Names, chc::PredVarId) -> bool,
    name_of: impl Fn(usize, usize, &str) -> String,
    owner_of: impl Fn(usize) -> Owner,
) -> Vec<chc::PredVarId> {
    let found: Vec<_> = params
        .iter()
        .enumerate()
        .flat_map(|(i, (own, ty))| {
            pred_vars(&ty.refinement)
                .into_iter()
                .map(move |(p, atom)| (i, own, p, atom))
        })
        .filter(|(_, _, p, _)| !names.preds.contains_key(p) && claims(names, *p))
        .collect();
    let mut named = Vec::new();
    for (k, (i, own, p, atom)) in found.iter().enumerate() {
        let args = atom
            .args
            .iter()
            .map(|t| match t {
                chc::Term::Var(rty::RefinedTypeVar::Existential(_)) => None,
                chc::Term::Var(v) => Some(var_name(params, own, v)),
                chc::Term::BoxCurrent(inner) => match &**inner {
                    chc::Term::Var(rty::RefinedTypeVar::Existential(_)) => None,
                    chc::Term::Var(v) => Some(var_name(params, own, v)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let info = PredInfo {
            name: name_of(k, found.len(), own),
            args,
            results: 0,
            order: None,
            owner: owner_of(*i),
        };
        names.preds.insert(*p, info);
        named.push(*p);
    }
    named
}

fn render_refinement(
    names: &Names,
    params: &[Param<'_>],
    own: &str,
    refinement: &rty::Refinement<rty::FunctionParamIdx>,
) -> Expr {
    let name = |v: &rty::RefinedTypeVar<rty::FunctionParamIdx>| var_name(params, own, v);
    let body = expr::of_body(&refinement.body, &name, &|p| names.pred_head(p));
    if !refinement.has_existentials() {
        return body;
    }
    let vars = refinement
        .existentials()
        .map(|(e, sort)| (existential_name(e), sort.display().to_string()))
        .collect();
    Expr::Quant("exists", vars, Box::new(body))
}

fn site_params(names: &Names, params: &[Param<'_>]) -> Vec<SiteParam> {
    params
        .iter()
        .map(|(own, ty)| SiteParam {
            name: own.clone(),
            ty: rust_type(&ty.ty.display().to_string()),
            refinement: render_refinement(names, params, own, &ty.refinement),
        })
        .collect()
}

/// The site of the contract of `def`, if it has a predicate variable over some value to infer.
pub fn contract_site(
    names: &mut Names,
    fn_name: &str,
    def: LocalDefId,
    body: &DefBody<'_>,
    span: Span,
    fn_ty: &rty::FunctionType,
) -> Option<Site> {
    let mut params: Vec<Param<'_>> = fn_ty
        .params
        .iter_enumerated()
        .map(|(idx, ty)| (body.param_name(idx.index()), ty))
        .collect();
    let param_count = params.len();
    let pre_count: usize = params
        .iter()
        .map(|(_, ty)| pred_vars(&ty.refinement).len())
        .sum();
    params.push(("result".to_owned(), &*fn_ty.ret));
    let preds = name_preds(
        names,
        &params,
        |names, p| names.made_in_contract(p, def),
        |_, _, own| match own {
            "result" => format!("{fn_name}.post"),
            _ if pre_count == 1 => format!("{fn_name}.pre"),
            _ => format!("{fn_name}.pre_{own}"),
        },
        |i| Owner::Contract {
            def,
            ret: i == param_count,
        },
    );
    if preds.iter().all(|p| names.preds[p].args.is_empty()) {
        return None;
    }
    Some(Site {
        kind: SiteKind::Contract,
        span,
        params: site_params(names, &params),
        preds,
        signature: None,
    })
}

/// The name of each parameter of a block's type: the local it holds, or the value a parameter of
/// the function had on entry, `old(x)` when the local `x` is also a parameter of the block.
fn block_param_names(body: &DefBody<'_>, ty: &BasicBlockType) -> Vec<String> {
    let fn_ty: &rty::FunctionType = ty.as_ref();
    let locals: Vec<String> = ty.locals().map(|l| body.local_name(l)).collect();
    fn_ty
        .params
        .indices()
        .map(|idx| match ty.param_kind(idx) {
            BasicBlockTypeParamKind::Local(local, _) => body.local_name(local),
            BasicBlockTypeParamKind::OuterFnParam(i) => {
                let name = body.param_name(i.index());
                if locals.contains(&name) {
                    format!("old({name})")
                } else {
                    name
                }
            }
            BasicBlockTypeParamKind::Synthetic => format!("__tmp_thrust_synthetic{}", idx.index()),
            BasicBlockTypeParamKind::Captured => format!("__tmp_thrust_captured{}", idx.index()),
        })
        .collect()
}

/// The site of the type of block `bb` of `def`, if it has a predicate variable to infer.
pub fn block_site(
    names: &mut Names,
    fn_name: &str,
    def: LocalDefId,
    body: &DefBody<'_>,
    bb: BasicBlock,
    ty: &BasicBlockType,
) -> Option<Site> {
    let fn_ty: &rty::FunctionType = ty.as_ref();
    let params: Vec<Param<'_>> = block_param_names(body, ty)
        .into_iter()
        .zip(fn_ty.params.iter())
        .collect();
    let loop_number = body.loop_number(bb);
    let is_loop = loop_number.is_some();
    let base = match loop_number {
        Some(n) => format!("{fn_name}.loop#{n}"),
        None => format!("{fn_name}.{bb:?}"),
    };
    let preds = name_preds(
        names,
        &params,
        |names, p| names.made_in_block(p, def, bb),
        |k, n, _| {
            if n == 1 {
                base.clone()
            } else {
                format!("{base}_{}", k + 1)
            }
        },
        |_| Owner::Block { def, bb },
    );
    if preds.iter().all(|p| names.preds[p].args.is_empty()) {
        return None;
    }
    let span = body.span(bb, None)?;
    let signature = whole_template(&params).filter(|(p, _)| preds.contains(p));
    if let Some((p, order)) = &signature {
        let info = names.preds.get_mut(p).unwrap();
        info.args = params.iter().map(|(own, _)| Some(own.clone())).collect();
        info.order = Some(order.clone());
    }
    Some(Site {
        kind: if is_loop {
            SiteKind::Loop(bb)
        } else {
            SiteKind::Block(bb)
        },
        span,
        params: site_params(names, &params),
        preds,
        signature: signature.map(|(p, _)| p),
    })
}

/// The predicate variable that is the whole template over `params`, with the order to show its
/// arguments in so that they follow `params`: one parameter's refinement is that variable applied
/// to every parameter once, and the others' are `true`.
fn whole_template(params: &[Param<'_>]) -> Option<(chc::PredVarId, Vec<usize>)> {
    let mut found = None;
    for (i, (_, ty)) in params.iter().enumerate() {
        let refinement = &ty.refinement;
        if refinement.is_top() {
            continue;
        }
        let ([atom], true, false) = (
            refinement.body.atoms.as_slice(),
            refinement.body.formula.is_top(),
            refinement.has_existentials(),
        ) else {
            return None;
        };
        let chc::Pred::Var(p) = atom.pred else {
            return None;
        };
        if found.is_some() {
            return None;
        }
        // The parameter each argument is.
        let positions: Option<Vec<usize>> = atom
            .args
            .iter()
            .map(|arg| {
                let var = match arg {
                    chc::Term::Var(v) => v,
                    chc::Term::BoxCurrent(inner) => match &**inner {
                        chc::Term::Var(v) => v,
                        _ => return None,
                    },
                    _ => return None,
                };
                match var {
                    rty::RefinedTypeVar::Value => Some(i),
                    rty::RefinedTypeVar::Free(idx) => Some(idx.index()),
                    rty::RefinedTypeVar::Existential(_) => None,
                }
            })
            .collect();
        found = Some((p, positions?));
    }
    let (p, positions) = found?;
    // Every parameter once: the k-th shown is the argument at the position holding parameter k.
    let order: Option<Vec<usize>> = (0..params.len())
        .map(|k| positions.iter().position(|&q| q == k))
        .collect();
    let order = order?;
    (positions.len() == params.len()).then_some((p, order))
}
