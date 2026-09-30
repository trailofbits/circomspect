use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::lattice::Lattice;

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
    /// Whether this key denotes every location denoted by `other`.
    #[must_use]
    pub fn covers(&self, other: &Self) -> bool {
        if self.root != other.root || self.instance != other.instance {
            return false;
        }
        if self.steps.len() > other.steps.len() {
            return false;
        }
        self.steps.iter().zip(&other.steps).all(|(left, right)| match (left, right) {
            (
                AccessKeyStep::Index(IndexKey::Symbolic(_) | IndexKey::Unknown),
                AccessKeyStep::Index(_),
            ) => true,
            (left, right) => left == right,
        })
    }

    fn widen_with(&self, other: &Self) -> Option<Self> {
        if self.root != other.root
            || self.instance != other.instance
            || self.steps.len() != other.steps.len()
        {
            return None;
        }
        let mut steps = Vec::with_capacity(self.steps.len());
        let mut widened = false;
        for (left, right) in self.steps.iter().zip(&other.steps) {
            if left == right {
                steps.push(left.clone());
            } else if let (AccessKeyStep::Index(_), AccessKeyStep::Index(_)) = (left, right) {
                steps.push(AccessKeyStep::Index(IndexKey::Unknown));
                widened = true;
            } else {
                return None;
            }
        }
        widened.then_some(Self { root: self.root, instance: self.instance, steps })
    }

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

/// May-dependencies ordered by the locations each key can denote.
///
/// The finite HIR access paths bound this domain. Symbolic indices are
/// represented by one wildcard, so concrete index values cannot cause an
/// infinite ascending chain in a loop.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MayAccessSet(BTreeSet<AccessKey>);

impl MayAccessSet {
    #[must_use]
    pub fn from_keys(keys: BTreeSet<AccessKey>) -> Self {
        let mut result = Self::default();
        for key in keys {
            result.insert(key);
        }
        result
    }

    pub fn iter(&self) -> impl Iterator<Item = &AccessKey> {
        self.0.iter()
    }

    pub fn insert(&mut self, mut key: AccessKey) {
        for step in &mut key.steps {
            if let AccessKeyStep::Index(index @ IndexKey::Symbolic(_)) = step {
                *index = IndexKey::Unknown;
            }
        }
        loop {
            if self.0.iter().any(|existing| existing.covers(&key)) {
                return;
            }
            let Some((existing, widened)) = self.0.iter().find_map(|existing| {
                existing.widen_with(&key).map(|widened| (existing.clone(), widened))
            }) else {
                break;
            };
            self.0.remove(&existing);
            key = widened;
        }
        self.0.retain(|existing| !key.covers(existing));
        self.0.insert(key);
    }
}

impl Lattice for MayAccessSet {
    fn bottom() -> Self {
        Self::default()
    }

    fn leq(&self, other: &Self) -> bool {
        self.0.iter().all(|key| other.0.iter().any(|candidate| candidate.covers(key)))
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        let old = self.clone();
        for key in &other.0 {
            self.insert(key.clone());
        }
        *self != old
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

    #[test]
    fn may_access_lattice_widens_concrete_indices_to_wildcards() {
        let field = FieldContext::for_curve(Curve::Bn254);
        let hir = component_paths("template Check(){signal input a[2];}").0;
        let root = hir.symbols().iter().find(|symbol| symbol.name == "a").unwrap().id;
        let key =
            |index| AccessKey { root, instance: None, steps: vec![AccessKeyStep::Index(index)] };
        let zero = key(IndexKey::Exact(field.canonical(0.into())));
        let one = key(IndexKey::Exact(field.canonical(1.into())));
        let wildcard = key(IndexKey::Unknown);
        let states = [
            MayAccessSet::default(),
            MayAccessSet::from_keys(BTreeSet::from([zero.clone()])),
            MayAccessSet::from_keys(BTreeSet::from([one.clone()])),
            MayAccessSet::from_keys(BTreeSet::from([zero, one])),
            MayAccessSet::from_keys(BTreeSet::from([wildcard])),
        ];
        assert!(states[1].leq(&states[4]));
        assert!(!states[4].leq(&states[1]));
        assert_eq!(states[3], states[4]);
        for left in &states {
            for right in &states {
                let mut joined = left.clone();
                let changed = joined.join_assign(right);
                assert_eq!(changed, joined != *left);
                assert!(left.leq(&joined) && right.leq(&joined));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(joined, reverse);
                for third in &states {
                    let mut first = joined.clone();
                    first.join_assign(third);
                    let mut second = right.clone();
                    second.join_assign(third);
                    let mut alternative = left.clone();
                    alternative.join_assign(&second);
                    assert_eq!(first, alternative);
                }
            }
        }
    }

    fn component_paths(source: &str) -> (HirProject, Vec<AccessPath>) {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-phase4-instances-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
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
