//! Certified scalar expressions bound to one HIR definition and selected field.

use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{DefinitionRef, ExprId, HirProject, ProjectIdentity};
use program_structure::utils::constants::Curve;

use crate::hir_facts::FieldValue;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ScalarExpressionEvidence {
    project: ProjectIdentity,
    definition: DefinitionRef,
    curve: Curve,
    values: BTreeMap<ExprId, ExactScalarResult>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ExactScalarResult {
    value: FieldValue,
    origin: ScalarOrigin,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ScalarOrigin {
    FunctionReturn { input_dependencies: BTreeSet<usize> },
    FlowAccess,
}

impl ScalarExpressionEvidence {
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

    pub(crate) fn call_value(&self, expression: ExprId) -> Option<&FieldValue> {
        let result = self.values.get(&expression)?;
        let ScalarOrigin::FunctionReturn { .. } = &result.origin else { return None };
        Some(&result.value)
    }

    pub(crate) fn call_input_dependencies(&self, expression: ExprId) -> Option<&BTreeSet<usize>> {
        let result = self.values.get(&expression)?;
        let ScalarOrigin::FunctionReturn { input_dependencies } = &result.origin else {
            return None;
        };
        Some(input_dependencies)
    }

    pub(crate) fn insert_call(
        &mut self,
        expression: ExprId,
        value: FieldValue,
        input_dependencies: BTreeSet<usize>,
    ) {
        self.values.insert(
            expression,
            ExactScalarResult {
                value,
                origin: ScalarOrigin::FunctionReturn { input_dependencies },
            },
        );
    }

    pub(crate) fn insert_access(&mut self, expression: ExprId, value: FieldValue) {
        self.values
            .insert(expression, ExactScalarResult { value, origin: ScalarOrigin::FlowAccess });
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
