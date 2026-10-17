use std::fmt;

use crate::chc::{Sort, TermVarIdx, Var};
use crate::pretty::PrettyDisplayExt;
use crate::rty::{self, ExistentialVarIdx};

#[derive(Debug, Clone)]
pub struct ClauseOrigin {
    pub environment: Vec<Entry>,
    pub body: Vec<Entry>,
    pub head: Entry,
}

#[derive(Debug, Clone)]
pub struct Entry {
    text: String,
    mappings: Vec<VarMapping>,
}

#[derive(Debug, Clone)]
pub struct VarMapping {
    source: String,
    chc_var: TermVarIdx,
    /// The variable of the analysis mapped, when it is one (not the value `ν`).
    var: Option<super::ErasedVar>,
}

impl Entry {
    pub fn binding<V: Var, T: Var>(variable: V, ty: &rty::RefinedType<T>) -> Self {
        Self {
            text: format!("{variable:?}: {}", ty.display()),
            mappings: Vec::new(),
        }
    }

    pub fn described(text: String) -> Self {
        Self {
            text,
            mappings: Vec::new(),
        }
    }

    pub fn parameter<V: Var>(variable: V, sort: &Sort) -> Self {
        Self {
            text: format!("{variable:?}: {}", sort.display()),
            mappings: Vec::new(),
        }
    }

    pub fn assumption<V: Var>(formula: &rty::Formula<V>) -> Self {
        Self {
            text: format!("_: {{ {} }}", formula.display()),
            mappings: Vec::new(),
        }
    }

    pub fn refinement<V: Var>(refinement: &rty::Refinement<V>) -> Self {
        Self {
            text: refinement.display().to_string(),
            mappings: Vec::new(),
        }
    }

    pub fn var_mapping<V: Var>(mut self, variable: V, chc_var: TermVarIdx) -> Self {
        self.add_var_mapping(variable, chc_var);
        self
    }

    pub fn add_var_mapping<V: Var>(&mut self, variable: V, chc_var: TermVarIdx) {
        self.mappings.push(VarMapping {
            source: format!("{variable:?}"),
            chc_var,
            var: Some(super::ErasedVar::new(variable)),
        });
    }

    /// Maps `variable`, kept as `described`, what it holds as the code that made it says.
    pub fn add_described_var_mapping<V: Var>(
        &mut self,
        variable: V,
        chc_var: TermVarIdx,
        described: super::ErasedVar,
    ) {
        self.mappings.push(VarMapping {
            source: format!("{variable:?}"),
            chc_var,
            var: Some(described),
        });
    }

    pub fn value_var_mapping(mut self, chc_var: TermVarIdx) -> Self {
        self.add_value_var_mapping(chc_var);
        self
    }

    pub fn add_value_var_mapping(&mut self, chc_var: TermVarIdx) {
        self.mappings.push(VarMapping {
            source: "ν".to_owned(),
            chc_var,
            var: None,
        });
    }

    pub fn existential_var_mapping(
        mut self,
        variable: ExistentialVarIdx,
        chc_var: TermVarIdx,
    ) -> Self {
        self.add_existential_var_mapping(variable, chc_var);
        self
    }

    pub fn add_existential_var_mapping(
        &mut self,
        variable: ExistentialVarIdx,
        chc_var: TermVarIdx,
    ) {
        self.mappings.push(VarMapping {
            source: variable.to_string(),
            chc_var,
            var: Some(super::ErasedVar::new(variable)),
        });
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn mappings(&self) -> &[VarMapping] {
        &self.mappings
    }
}

impl VarMapping {
    pub fn chc_var(&self) -> TermVarIdx {
        self.chc_var
    }

    /// The variable of the analysis mapped, for the code that knows its type.
    pub fn var(&self) -> Option<&super::ErasedVar> {
        self.var.as_ref()
    }
}

impl fmt::Display for VarMapping {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} -> {}", self.source, self.chc_var)
    }
}
