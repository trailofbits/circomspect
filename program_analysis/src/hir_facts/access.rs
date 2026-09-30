use std::collections::BTreeMap;

use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, ComponentId, ExprId, HirProject, PortId, SymbolId,
};

use super::field::{FieldContext, FieldValue};
use super::forward::eval_expression;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IndexKey {
    Exact(FieldValue),
    Symbolic(ExprId),
    Unknown,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AccessKeyStep {
    Index(IndexKey),
    Port(PortId),
    Tag(SymbolId),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AccessKey {
    pub root: SymbolId,
    pub instance: Option<ComponentId>,
    pub steps: Vec<AccessKeyStep>,
}

impl AccessKey {
    /// Alias conservatively at symbolic indices and compare every typed port.
    #[must_use]
    pub fn may_alias(&self, other: &Self) -> bool {
        if self.root != other.root || self.instance != other.instance {
            return false;
        }
        for (left, right) in self.steps.iter().zip(&other.steps) {
            match (left, right) {
                (AccessKeyStep::Index(IndexKey::Symbolic(_)), AccessKeyStep::Index(_))
                | (AccessKeyStep::Index(_), AccessKeyStep::Index(IndexKey::Symbolic(_)))
                | (AccessKeyStep::Index(IndexKey::Unknown), AccessKeyStep::Index(_))
                | (AccessKeyStep::Index(_), AccessKeyStep::Index(IndexKey::Unknown)) => {}
                (left, right) if left == right => {}
                _ => return false,
            }
        }
        true
    }

    #[must_use]
    pub fn exact_alias(&self, other: &Self) -> bool {
        self == other
            && self.steps.iter().all(|step| match step {
                AccessKeyStep::Index(IndexKey::Symbolic(_) | IndexKey::Unknown) => false,
                AccessKeyStep::Index(IndexKey::Exact(_))
                | AccessKeyStep::Port(_)
                | AccessKeyStep::Tag(_) => true,
            })
    }
}

pub fn key_for_path(
    hir: &HirProject,
    field: &FieldContext,
    path: &AccessPath,
    variables: &BTreeMap<SymbolId, FieldValue>,
) -> AccessKey {
    let instance =
        hir.components().iter().find(|item| item.symbol == path.root).map(|item| item.id);
    let mut steps = Vec::with_capacity(path.steps.len());
    for step in &path.steps {
        let key = match step {
            AccessStep::Index { index: ArrayIndex::Constant(text), .. } => {
                let index = field.parse(text).map_or(IndexKey::Unknown, IndexKey::Exact);
                AccessKeyStep::Index(index)
            }
            AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => {
                let index = eval_expression(hir, field, *id, variables)
                    .map_or(IndexKey::Symbolic(*id), IndexKey::Exact);
                AccessKeyStep::Index(index)
            }
            AccessStep::Port { port, .. } => AccessKeyStep::Port(*port),
            AccessStep::Tag { symbol, .. } => AccessKeyStep::Tag(*symbol),
        };
        steps.push(key);
    }
    AccessKey { root: path.root, instance, steps }
}
