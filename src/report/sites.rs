//! The places whose refinements Thrust infers, and a readable name for each predicate variable
//! they carry.
//!
//! A predicate variable belongs to the template it was made for, which the spans it was made in
//! tell: a function's contract when the function has none written, a basic block's type, or the
//! result of a call. A loop header's block type is the loop's invariant; the other blocks' types
//! are intermediate steps of the analysis.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{BasicBlock, Local};
use rustc_span::def_id::LocalDefId;
use rustc_span::Span;

use crate::analyze::TemplateSite;
use crate::chc;
use crate::chc::debug::ErasedVar;
use crate::refine::{BasicBlockType, BasicBlockTypeParamKind, Var, VarPath};
use crate::rty;
use crate::rty::RefinedTypeVar;

use super::body::DefBody;
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
    /// The groups the arguments are shown in (see [`expr::grouped`]): for a call's result, the
    /// result, the call's arguments, and the other variables live there.
    pub groups: Vec<usize>,
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

/// What the analysis tells of the call ending a block, for the predicate variables made for its
/// result.
pub struct CallAt {
    /// The name of the result's variable: `f.g#k` for the `k`-th call to `g` in `f`.
    pub name: String,
    /// The local the result goes to.
    pub result: String,
    /// The locals the call's arguments are, in order.
    pub arguments: Vec<Local>,
}

#[derive(Debug, Default)]
pub struct Names {
    pub preds: HashMap<chc::PredVarId, PredInfo>,
    /// Where the analysis made each template's predicate variable.
    sites: HashMap<chc::PredVarId, TemplateSite>,
    /// The variable each argument of a template's predicate variable is.
    vars: HashMap<chc::PredVarId, Vec<Option<ErasedVar>>>,
    /// The query's names of the system's predicate variables.
    query_names: HashSet<String>,
    /// The predicate variables without arguments that every solution makes true: those a clause
    /// derives from nothing but others of them, such as a function's entry being reached. A
    /// constraint's premise that applies one says nothing and is not shown.
    pub always_true: HashSet<chc::PredVarId>,
}

/// The predicate variables without arguments that clauses with nothing but such variables in
/// their bodies derive, starting from none: the least solution makes them true, so every
/// solution does.
fn always_true(system: &chc::System) -> HashSet<chc::PredVarId> {
    let mut found = HashSet::new();
    loop {
        let before = found.len();
        for clause in &system.clauses {
            let chc::Pred::Var(head) = clause.head.pred else {
                continue;
            };
            let derived = clause.head.args.is_empty()
                && clause.head.guard.is_none()
                && clause.body.formula.is_top()
                && clause.body.atoms.iter().all(|atom| match atom.pred {
                    chc::Pred::Var(p) => atom.guard.is_none() && found.contains(&p),
                    _ => atom.pred.is_top(),
                });
            if derived {
                found.insert(head);
            }
        }
        if found.len() == before {
            return found;
        }
    }
}

impl Names {
    pub fn new(
        system: &chc::System,
        sites: &HashMap<chc::PredVarId, TemplateSite>,
        vars: &HashMap<chc::PredVarId, Vec<Option<ErasedVar>>>,
    ) -> Self {
        Names {
            preds: HashMap::new(),
            sites: sites.clone(),
            vars: vars.clone(),
            query_names: system.pred_vars.indices().map(|p| p.to_string()).collect(),
            always_true: always_true(system),
        }
    }

    /// How `p` is shown.
    pub fn pred_head(&self, p: chc::PredVarId) -> PredHead {
        match self.preds.get(&p) {
            Some(info) => PredHead {
                name: info.name.clone(),
                groups: info.groups.clone(),
                order: info.order.clone(),
            },
            None => PredHead {
                name: p.to_string(),
                groups: Vec::new(),
                order: None,
            },
        }
    }

    /// Whether `name` is how the query names a predicate variable of the system.
    pub fn is_pred_var(&self, name: &str) -> bool {
        self.query_names.contains(name)
    }

    fn made_in_contract(&self, p: chc::PredVarId, def: LocalDefId) -> bool {
        self.sites.get(&p) == Some(&TemplateSite::Contract(def))
    }

    fn made_in_block(&self, p: chc::PredVarId, def: LocalDefId, bb: BasicBlock) -> bool {
        self.sites.get(&p) == Some(&TemplateSite::Block(def, bb))
    }

    /// A name not given yet: `base`, or `base_2`, `base_3`, ….
    fn fresh(&self, base: String) -> String {
        let used: HashSet<&str> = self.preds.values().map(|i| i.name.as_str()).collect();
        (1..)
            .map(|n| match n {
                1 => base.clone(),
                n => format!("{base}_{n}"),
            })
            .find(|name| !used.contains(name.as_str()))
            .unwrap()
    }

    /// Names the predicate variables made in the code of a block: the result of the call ending
    /// it, `call_at(def, bb)` telling of the call and `path_name(def, path)` naming what a
    /// variable holds, and the refinements nested in the result's type. The result's template is
    /// over the variables in scope at the call, the nested ones over none; its arguments are
    /// shown as the result, the call's arguments, and the other variables.
    pub fn name_calls(
        &mut self,
        call_at: impl Fn(LocalDefId, BasicBlock) -> Option<CallAt>,
        path_name: impl Fn(LocalDefId, &VarPath) -> String,
    ) {
        let mut made: Vec<(chc::PredVarId, LocalDefId, BasicBlock)> = self
            .sites
            .iter()
            .filter(|(p, _)| !self.preds.contains_key(p))
            .filter_map(|(p, site)| match *site {
                TemplateSite::Code(def, bb) => Some((*p, def, bb)),
                _ => None,
            })
            .collect();
        made.sort_by_key(|(p, _, _)| p.index());
        for (p, def, bb) in made {
            let Some(call) = call_at(def, bb) else {
                continue;
            };
            let args: Vec<Option<CallArg>> = self.vars[&p].iter().map(CallArg::of).collect();
            let info = if args.iter().all(Option::is_some) {
                let args: Vec<CallArg> = args.into_iter().flatten().collect();
                self.call_result(def, &call, &args, |path| path_name(def, path))
            } else {
                PredInfo {
                    name: self.fresh(format!("{}.inner", call.name)),
                    args: vec![None; args.len()],
                    groups: Vec::new(),
                    order: None,
                    owner: Owner::Other { def },
                }
            };
            self.preds.insert(p, info);
        }
    }

    fn call_result(
        &self,
        def: LocalDefId,
        call: &CallAt,
        args: &[CallArg],
        path_name: impl Fn(&VarPath) -> String,
    ) -> PredInfo {
        let is_result = |k: usize| matches!(args[k], CallArg::Result);
        let local = |k: usize| match &args[k] {
            CallArg::Held(path) if path.steps.is_empty() => Some(path.local),
            _ => None,
        };
        let mut order: Vec<usize> = (0..args.len()).filter(|&k| is_result(k)).collect();
        let results = order.len();
        for argument in &call.arguments {
            let found =
                (0..args.len()).find(|&k| local(k) == Some(*argument) && !order.contains(&k));
            order.extend(found);
        }
        let arguments = order.len() - results;
        let rest: Vec<usize> = (0..args.len()).filter(|k| !order.contains(k)).collect();
        order.extend(rest);
        let names = order
            .iter()
            .map(|&k| match &args[k] {
                CallArg::Result => Some(call.result.clone()),
                CallArg::Held(path) => Some(path_name(path)),
                CallArg::Other => None,
            })
            .collect();
        PredInfo {
            name: self.fresh(call.name.clone()),
            args: names,
            groups: vec![results, arguments],
            order: Some(order),
            owner: Owner::Other { def },
        }
    }
}

/// An argument of the template of a call's result.
enum CallArg {
    /// The result itself.
    Result,
    /// A value of a local in scope at the call.
    Held(VarPath),
    /// A variable in scope that holds no local's value.
    Other,
}

impl CallArg {
    /// What the template's argument `var` is; `None` when it is not over the variables in scope,
    /// as a refinement nested in the result's type is not.
    fn of(var: &Option<ErasedVar>) -> Option<CallArg> {
        let var = var.as_ref()?;
        if let Some(path) = var.downcast_ref::<VarPath>() {
            return Some(CallArg::Held(path.clone()));
        }
        if var.downcast_ref::<Var>().is_some() {
            return Some(CallArg::Other);
        }
        Some(match var.downcast_ref::<RefinedTypeVar<Var>>()? {
            RefinedTypeVar::Value => CallArg::Result,
            _ => CallArg::Other,
        })
    }
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
/// The refined types nested in `ty`'s type arguments, each with its path from `ty`: the `k`-th
/// argument at `.argk`, its arguments at `.argk.argj`.
fn nested_refinements<'a, T>(
    ty: &'a rty::Type<T>,
    path: &str,
    out: &mut Vec<(String, &'a rty::RefinedType<T>)>,
) {
    let children: Vec<&rty::RefinedType<T>> = match ty {
        rty::Type::Pointer(p) => vec![&*p.elem],
        rty::Type::Tuple(t) => t.elems.iter().collect(),
        rty::Type::Array(a) => vec![&*a.index, &*a.elem],
        rty::Type::Seq(e) => vec![&**e],
        rty::Type::Enum(e) => e.args.iter().collect(),
        _ => Vec::new(),
    };
    for (k, child) in children.into_iter().enumerate() {
        let path = format!("{path}.arg{k}");
        out.push((path.clone(), child));
        nested_refinements(&child.ty, &path, out);
    }
}

/// Names the predicate variables of one template that `claims` accepts, `params` being its
/// parameters by name, and returns them in order. `name_of(k, n, own)` is the name of the `k`-th
/// of the `n` variables found in the refinement of the parameter named `own`; `owner_of(i)` is
/// the owner of those in parameter `i`. A variable in a refinement nested in a parameter's type
/// (the `Some` value of an `Option`) is named after the parameter's with the path to it,
/// `next.post.arg0`, and its value after the parameter's with the same path.
fn name_preds(
    names: &mut Names,
    params: &[Param<'_>],
    claims: impl Fn(&Names, chc::PredVarId) -> bool,
    name_of: impl Fn(usize, usize, &str) -> String,
    owner_of: impl Fn(usize) -> Owner,
) -> Vec<chc::PredVarId> {
    let top: Vec<_> = params
        .iter()
        .enumerate()
        .flat_map(|(i, (own, ty))| {
            pred_vars(&ty.refinement)
                .into_iter()
                .map(move |(p, atom)| (i, own, p, atom))
        })
        .filter(|(_, _, p, _)| !names.preds.contains_key(p) && claims(names, *p))
        .collect();
    let mut found: Vec<_> = top
        .iter()
        .enumerate()
        .map(|(k, (i, own, p, atom))| (*i, (*own).clone(), name_of(k, top.len(), own), *p, *atom))
        .collect();
    for (i, (own, ty)) in params.iter().enumerate() {
        let mut nested = Vec::new();
        nested_refinements(&ty.ty, "", &mut nested);
        for (path, refined) in nested {
            for (p, atom) in pred_vars(&refined.refinement) {
                if names.preds.contains_key(&p) || !claims(names, p) {
                    continue;
                }
                let name = format!("{}{path}", name_of(0, 1, own));
                found.push((i, format!("{own}{path}"), name, p, atom));
            }
        }
    }
    let mut named = Vec::new();
    for (i, own, name, p, atom) in found {
        let args = atom
            .args
            .iter()
            .map(|t| match t {
                chc::Term::Var(rty::RefinedTypeVar::Existential(_)) => None,
                chc::Term::Var(v) => Some(var_name(params, &own, v)),
                chc::Term::BoxCurrent(inner) => match &**inner {
                    chc::Term::Var(rty::RefinedTypeVar::Existential(_)) => None,
                    chc::Term::Var(v) => Some(var_name(params, &own, v)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let info = PredInfo {
            name,
            args,
            groups: Vec::new(),
            order: None,
            owner: owner_of(i),
        };
        names.preds.insert(p, info);
        named.push(p);
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
        .map(|(e, sort)| (existential_name(e), expr::sort_name(sort)))
        .collect();
    Expr::Quant("exists", vars, Box::new(body))
}

fn site_params(names: &Names, params: &[Param<'_>]) -> Vec<SiteParam> {
    params
        .iter()
        .map(|(own, ty)| SiteParam {
            name: own.clone(),
            ty: expr::sort_name(&ty.ty.to_sort()),
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
