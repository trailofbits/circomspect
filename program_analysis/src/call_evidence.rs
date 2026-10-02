//! Exact call values bound to one HIR definition and selected field.

use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{DefinitionRef, ExprId, HirProject, ProjectIdentity};
use program_structure::utils::constants::Curve;

use crate::hir_facts::FieldValue;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExactCallResults {
    project: ProjectIdentity,
    definition: DefinitionRef,
    curve: Curve,
    values: BTreeMap<ExprId, ExactCallResult>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExactCallResult {
    value: FieldValue,
    input_dependencies: BTreeSet<usize>,
}

impl ExactCallResults {
    pub(crate) fn empty(hir: &HirProject, definition: DefinitionRef, curve: Curve) -> Self {
        Self { project: hir.identity(), definition, curve, values: BTreeMap::new() }
    }

    pub(crate) fn belongs_to(
        &self,
        hir: &HirProject,
        definition: DefinitionRef,
        curve: &Curve,
    ) -> bool {
        self.belongs_to_definition(hir, definition) && &self.curve == curve
    }

    pub(crate) fn belongs_to_definition(
        &self,
        hir: &HirProject,
        definition: DefinitionRef,
    ) -> bool {
        self.project == hir.identity() && self.definition == definition
    }

    pub(crate) fn value(&self, expression: ExprId) -> Option<&FieldValue> {
        self.values.get(&expression).map(|result| &result.value)
    }

    pub(crate) fn input_dependencies(&self, expression: ExprId) -> Option<&BTreeSet<usize>> {
        self.values.get(&expression).map(|result| &result.input_dependencies)
    }

    pub(crate) fn insert(
        &mut self,
        expression: ExprId,
        value: FieldValue,
        input_dependencies: BTreeSet<usize>,
    ) {
        self.values.insert(expression, ExactCallResult { value, input_dependencies });
    }

    pub(crate) fn merge(&mut self, other: &Self) -> Result<bool, ()> {
        if !self.belongs_to_scope(other) {
            return Err(());
        }
        let mut changed = false;
        for (expression, value) in &other.values {
            match self.values.get(expression) {
                Some(previous) if previous != value => return Err(()),
                Some(_) => {}
                None => {
                    self.values.insert(*expression, value.clone());
                    changed = true;
                }
            }
        }
        Ok(changed)
    }

    fn belongs_to_scope(&self, other: &Self) -> bool {
        self.project == other.project
            && self.definition == other.definition
            && self.curve == other.curve
    }
}
