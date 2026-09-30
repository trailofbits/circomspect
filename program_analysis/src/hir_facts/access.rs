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

#[cfg(test)]
mod tests {
    use super::*;
    use parser::hir::{lower_project, ExprKind};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;
    use std::fs;

    fn component_paths(source: &str) -> (HirProject, Vec<AccessPath>) {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-instances-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        fs::write(&file, source).unwrap();
        let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let project = lower_project(&loaded);
        assert!(project.syntax_diagnostics.is_empty());
        assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
        let paths = project
            .hir
            .expressions()
            .iter()
            .filter_map(|expr| match &expr.kind {
                ExprKind::Access(path) if path.component_output => Some(path.clone()),
                _ => None,
            })
            .collect();
        (project.hir, paths)
    }

    #[test]
    fn distinct_instances_and_array_elements_never_alias() {
        let field = FieldContext::for_curve(Curve::Bn254);
        let (hir, paths) = component_paths(
            "template Child(){signal output out; out <== 1;} \
             template Check(){component c0=Child(); component c1=Child(); \
             signal output z; z <-- c0.out+c1.out;}",
        );
        assert_eq!(paths.len(), 2);
        let first = key_for_path(&hir, &field, &paths[0], &BTreeMap::new());
        let second = key_for_path(&hir, &field, &paths[1], &BTreeMap::new());
        assert_ne!(first.instance, second.instance);
        assert!(!first.may_alias(&second));

        let (hir, paths) = component_paths(
            "template Child(){signal output out; out <== 1;} \
             template Check(){component c[2]; c[0]=Child(); c[1]=Child(); \
             signal input i; signal output z; z <-- c[0].out+c[1].out+c[i].out;}",
        );
        assert_eq!(paths.len(), 3);
        let keys: Vec<_> =
            paths.iter().map(|path| key_for_path(&hir, &field, path, &BTreeMap::new())).collect();
        assert!(!keys[0].may_alias(&keys[1]));
        assert!(keys[2].may_alias(&keys[0]));
        assert!(keys[2].may_alias(&keys[1]));
        assert!(!keys[2].exact_alias(&keys[0]));
    }
}
