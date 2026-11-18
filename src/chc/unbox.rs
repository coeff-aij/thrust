//! An optimization that removes `Box` sorts and terms from a CHC system.

use super::*;

fn unbox_term<V>(term: Term<V>) -> Term<V> {
    let term = match term {
        Term::Box(t) | Term::BoxCurrent(t) => return unbox_term(*t),
        Term::ArrayEmpty(s1, s2) => Term::ArrayEmpty(unbox_sort(s1), unbox_sort(s2)),
        Term::SeqEmpty(s) => Term::SeqEmpty(unbox_sort(s)),
        Term::DatatypeCtor(s1, s2, args) => Term::DatatypeCtor(unbox_datatype_sort(s1), s2, args),
        Term::DatatypeSelector(sel, arg) => {
            let sel = Selector {
                sort: unbox_datatype_sort(sel.sort),
                field: unbox_sort(sel.field),
                ..*sel
            };
            Term::DatatypeSelector(Box::new(sel), arg)
        }
        Term::UserDefinedFn(symbol, sort, args) => {
            Term::UserDefinedFn(symbol, unbox_sort(sort), args)
        }
        Term::ForallFn(pred, args) => Term::ForallFn(unbox_forall_pred_var_def(pred), args),
        Term::UserQuantifiedVar(sort, var) => Term::UserQuantifiedVar(unbox_sort(sort), var),
        Term::ArrayLambda(var, sort, t) => Term::ArrayLambda(var, unbox_sort(sort), t),
        term @ (Term::Null
        | Term::ForallDefault(_)
        | Term::Var(_)
        | Term::Bool(_)
        | Term::Int(_)
        | Term::String(_)
        | Term::Mut(..)
        | Term::MutCurrent(_)
        | Term::MutFinal(_)
        | Term::App(..)
        | Term::Tuple(_)
        | Term::TupleProj(..)
        | Term::DatatypeDiscr(..)
        | Term::IntToBitVec { .. }) => term,
    };
    term.map_subterms(unbox_term)
}

fn unbox_matcher_pred(pred: MatcherPred) -> Pred {
    let MatcherPred {
        datatype_symbol,
        datatype_args,
    } = pred;
    let datatype_args = datatype_args.into_iter().map(unbox_sort).collect();
    Pred::Matcher(MatcherPred {
        datatype_symbol,
        datatype_args,
    })
}

fn unbox_pred(pred: Pred) -> Pred {
    match pred {
        Pred::Known(pred) => Pred::Known(pred),
        Pred::Var(pred) => Pred::Var(pred),
        Pred::Matcher(pred) => unbox_matcher_pred(pred),
        Pred::UserDefined(pred) => Pred::UserDefined(pred),
        Pred::ForallPred(pred) => Pred::ForallPred(unbox_forall_pred_var_def(pred)),
        Pred::Tester(ctor) => Pred::Tester(ctor),
    }
}

fn unbox_atom<V>(atom: Atom<V>) -> Atom<V> {
    let Atom { guard, pred, args } = atom;
    let guard = guard.map(|fo| Box::new(unbox_formula(*fo)));
    let pred = unbox_pred(pred);
    let args = args.into_iter().map(unbox_term).collect();
    Atom { guard, pred, args }
}

fn unbox_datatype_sort(sort: DatatypeSort) -> DatatypeSort {
    let DatatypeSort { symbol, args } = sort;
    let args = args.into_iter().map(unbox_sort).collect();
    DatatypeSort { symbol, args }
}

pub fn unbox_sort(sort: Sort) -> Sort {
    match sort {
        Sort::Box(inner) => unbox_sort(*inner),
        sort @ (Sort::Null
        | Sort::Int
        | Sort::BitVec { .. }
        | Sort::Bool
        | Sort::String
        | Sort::Param(_)
        | Sort::Mut(_)
        | Sort::Seq(_)
        | Sort::Tuple(_)
        | Sort::Array(..)
        | Sort::Datatype(_)
        | Sort::Forall(_)) => sort.map_children(unbox_sort),
    }
}

pub fn unbox_formula<V>(formula: Formula<V>) -> Formula<V> {
    let formula = match formula {
        Formula::Atom(atom) => return Formula::Atom(unbox_atom(atom)),
        Formula::Exists(vars, fo) => Formula::Exists(unbox_quantified_vars(vars), fo),
        Formula::Forall(vars, fo) => Formula::Forall(unbox_quantified_vars(vars), fo),
        formula @ (Formula::Not(_) | Formula::And(_) | Formula::Or(_) | Formula::Implies(..)) => {
            formula
        }
    };
    formula.map_subformulas(unbox_formula)
}

fn unbox_quantified_vars(
    vars: Vec<(UserQuantifiedVarId, Sort)>,
) -> Vec<(UserQuantifiedVarId, Sort)> {
    vars.into_iter().map(|(v, s)| (v, unbox_sort(s))).collect()
}

fn unbox_body(body: Body) -> Body {
    let Body { atoms, formula } = body;
    let atoms = atoms.into_iter().map(unbox_atom).collect();
    let formula = unbox_formula(formula);
    Body { atoms, formula }
}

fn unbox_clause(clause: Clause) -> Clause {
    let Clause {
        vars,
        head,
        body,
        debug_info,
        origin,
    } = clause;
    let vars = vars.into_iter().map(unbox_sort).collect();
    let head = unbox_atom(head);
    let body = unbox_body(body);
    Clause {
        vars,
        head,
        body,
        debug_info,
        origin,
    }
}

fn unbox_pred_var_def(pred_var_def: PredVarDef) -> PredVarDef {
    let PredVarDef { sig, debug_info } = pred_var_def;
    let sig = sig.into_iter().map(unbox_sort).collect();
    PredVarDef { sig, debug_info }
}

fn unbox_datatype_selector(selector: DatatypeSelector) -> DatatypeSelector {
    let DatatypeSelector { symbol, sort } = selector;
    let sort = unbox_sort(sort);
    DatatypeSelector { symbol, sort }
}

fn unbox_datatype_ctor(ctor: DatatypeCtor) -> DatatypeCtor {
    let DatatypeCtor {
        symbol,
        selectors,
        discriminant,
    } = ctor;
    let selectors = selectors.into_iter().map(unbox_datatype_selector).collect();
    DatatypeCtor {
        symbol,
        selectors,
        discriminant,
    }
}

fn unbox_datatype(datatype: Datatype) -> Datatype {
    let Datatype {
        symbol,
        params,
        ctors,
    } = datatype;
    let ctors = ctors.into_iter().map(unbox_datatype_ctor).collect();
    Datatype {
        symbol,
        params,
        ctors,
    }
}

fn unbox_user_defined_pred_def(user_defined_pred_def: UserDefinedPredDef) -> UserDefinedPredDef {
    let UserDefinedPredDef {
        symbol,
        sig,
        body,
        sort_subst,
        dependencies,
        decreases,
        result_facts,
    } = user_defined_pred_def;
    let sig = sig
        .into_iter()
        .map(|(name, sort)| (name, unbox_sort(sort)))
        .collect();
    let sort_subst = sort_subst
        .into_iter()
        .map(|(idx, sort)| (idx, unbox_sort(sort)))
        .collect();
    let body = match body {
        UserDefinedPredBody::Raw(s) => UserDefinedPredBody::Raw(s),
        UserDefinedPredBody::Derived => UserDefinedPredBody::Derived,
        UserDefinedPredBody::Formula(formula) => {
            UserDefinedPredBody::Formula(unbox_formula(formula))
        }
        UserDefinedPredBody::Term(sort, term) => {
            UserDefinedPredBody::Term(unbox_sort(sort), unbox_term(term))
        }
    };
    UserDefinedPredDef {
        symbol,
        sig,
        body,
        sort_subst,
        dependencies,
        decreases: decreases.map(unbox_term),
        result_facts: result_facts.map(unbox_formula),
    }
}

fn unbox_forall_pred_var_def(pred: ForallPred) -> ForallPred {
    let type_parameters = pred.type_parameters.into_iter().map(unbox_sort).collect();
    let params = pred.params.into_iter().map(unbox_sort).collect();
    ForallPred {
        inner: pred.inner,
        type_arguments: pred.type_arguments,
        type_parameters,
        params,
        result: unbox_sort(pred.result),
    }
}

/// Remove all `Box` sorts and `Box`/`BoxCurrent` terms from the system.
///
/// The box values in Thrust represent an owned pointer, but are logically equivalent to the inner type.
/// This pass removes them to reduce the complexity of the CHCs sent to the solver.
/// This function traverses a [`System`] and removes all `Box` related constructs.
pub fn unbox(system: System) -> System {
    let System {
        raw_commands,
        datatypes,
        user_defined_pred_defs,
        clauses,
        pred_vars,
        forall_sorts,
        num_forall_sort_idx,
        type_params_reverse,
        forall_pred_vars,
        laws,
        candidate_atoms,
        user_quantified_var_count,
        self_defined_pred_vars,
        user_quantified_var_names,
        opaque_preds,
        defined_copies,
    } = system;
    let datatypes = datatypes.into_iter().map(unbox_datatype).collect();
    let clauses = clauses.into_iter().map(unbox_clause).collect();
    let pred_vars = pred_vars.into_iter().map(unbox_pred_var_def).collect();
    let user_defined_pred_defs = user_defined_pred_defs
        .into_iter()
        .map(unbox_user_defined_pred_def)
        .collect();
    let forall_pred_vars = forall_pred_vars
        .into_iter()
        .map(unbox_forall_pred_var_def)
        .collect();
    let laws = laws
        .into_iter()
        .map(|(pred, laws)| {
            let laws = laws.into_iter().map(unbox_formula).collect();
            (unbox_forall_pred_var_def(pred), laws)
        })
        .collect();
    let candidate_atoms = candidate_atoms
        .into_iter()
        .map(|CandidateAtoms { pred, atoms }| CandidateAtoms {
            pred,
            atoms: atoms.into_iter().map(unbox_formula).collect(),
        })
        .collect();
    System {
        raw_commands,
        datatypes,
        user_defined_pred_defs,
        clauses,
        pred_vars,
        forall_sorts,
        num_forall_sort_idx,
        type_params_reverse,
        forall_pred_vars,
        laws,
        candidate_atoms,
        user_quantified_var_count,
        self_defined_pred_vars,
        user_quantified_var_names,
        opaque_preds,
        defined_copies,
    }
}
