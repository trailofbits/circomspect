//! Certified source accesses for consumers that need exact storage identities.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::solver::SolveResult;
use parser::hir::{AccessPath, AccessStep, PortId, SymbolKind};
use num_traits::ToPrimitive;

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::access::key_for_path;
use crate::hir_facts::{
    AccessHandle, AccessKey, AccessKeyStep, AnalysisFacts, Fact, FactBlocker, IndexKey, Range,
    VisitAccesses,
};

impl AnalysisFacts<'_> {
    /// Read exact source indices without claiming that either port schema accepts them.
    /// The provider must subsequently check the caller instance and callee port bounds.
    pub(crate) fn source_component_port_indices(
        &self,
        path: &AccessPath,
    ) -> Result<(PortId, Vec<usize>), FactBlocker> {
        if let Some(blocker) = self.validate_query_path(path, false) {
            return Err(blocker);
        }
        let mut port = None;
        let mut indices = Vec::new();
        for step in &path.steps {
            match step {
                AccessStep::Port { port: selected, .. } => {
                    if port.replace(*selected).is_some() {
                        return Err(FactBlocker::AggregateAccess);
                    }
                }
                AccessStep::Index { index, .. } if port.is_some() => {
                    let index =
                        self.access_index_value(index).map_err(|_| FactBlocker::AggregateAccess)?;
                    indices.push(index.to_usize().ok_or(FactBlocker::AggregateAccess)?);
                }
                AccessStep::Index { .. } => {}
                AccessStep::Tag { .. } => return Err(FactBlocker::AggregateAccess),
            }
        }
        Ok((port.ok_or(FactBlocker::AggregateAccess)?, indices))
    }

    pub(crate) fn applied_component_key(
        &self,
        applied: &crate::interprocedural::AppliedComponentPort,
    ) -> Fact<AccessKey> {
        if self.evidence_binding.as_ref() != Some(applied.caller_evidence())
            || !applied.handle().matches_context(applied.caller_evidence().context())
        {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let key = key_for_path(self.hir, self.field, applied.handle().path(), &BTreeMap::new());
        if !key.exact_alias(&key) {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        Fact::known(key)
    }

    /// Read the storage key of a provider-bound component handle. Local port and
    /// caller instance bounds were checked when the handle was constructed.
    pub(crate) fn component_handle_key(&self, handle: &AccessHandle) -> Fact<AccessKey> {
        let Some(evidence) = &self.evidence_binding else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        if handle.definition != self.definition()
            || handle.curve != *self.field.curve()
            || !handle.matches_context(evidence.context())
            || handle.component().is_none()
        {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let key = key_for_path(self.hir, self.field, handle.path(), &BTreeMap::new());
        if !key.exact_alias(&key) {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        Fact::known(key)
    }

    pub(crate) fn exact_closed_component_key(
        &self,
        path: &AccessPath,
        site: NodeId,
        ports: &crate::interprocedural::ValidatedComponentPorts,
    ) -> Fact<AccessKey> {
        if self.evidence_binding.as_ref() != Some(ports.evidence()) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        if let Some(blocker) = self.validate_query_path(path, false) {
            return Fact::blocked(BTreeSet::from([blocker]));
        }
        if !self.source_path_at_site(path, site) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let SolveResult::Complete(_) = &self.forward else {
            return Fact::blocked(self.forward_completion_blockers());
        };
        let Some(values) = self.site_state(site).and_then(|state| state.variables()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let key = key_for_path(self.hir, self.field, path, values);
        if ports.contains_access(&key) {
            Fact::known(key)
        } else {
            self.exact_access_key_at(path, site)
        }
    }

    /// Identify one owned scalar storage path with proved dimensions and exact indices.
    ///
    /// Symbolic index syntax is accepted only when its value is certified across every
    /// evaluation site. The key identifies storage; it does not prove reachability,
    /// witness assignment, constraint incidence, or successful execution of the definition.
    pub fn exact_access_key(&self, path: &AccessPath) -> Fact<AccessKey> {
        self.certify_access_key(path, false)
    }

    /// Identify a source access using checked static indices or certified site values.
    ///
    /// Static addresses do not depend on forward value propagation. An induction
    /// index must be exact and in bounds at this site. This proves neither that
    /// the site executes nor that the same key is used at other sites.
    pub(crate) fn exact_access_key_at(&self, path: &AccessPath, site: NodeId) -> Fact<AccessKey> {
        if let Some(blocker) = self.validate_query_path(path, false) {
            return Fact::blocked(BTreeSet::from([blocker]));
        }
        if !self.source_path_at_site(path, site) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        if !self.scalar_storage_path(path) {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        let SolveResult::Complete(_) = &self.forward else {
            if path.steps.iter().all(|step| match step {
                AccessStep::Index { index: parser::hir::ArrayIndex::Symbolic(_), .. } => false,
                AccessStep::Index { index: parser::hir::ArrayIndex::Constant(_), .. }
                | AccessStep::Port { .. }
                | AccessStep::Tag { .. } => true,
            }) {
                return self.exact_access_key(path);
            }
            return Fact::blocked(self.forward_completion_blockers());
        };
        let Some(values) = self.site_state(site).and_then(|state| state.variables()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let key = key_for_path(self.hir, self.field, path, values);
        if let Err(blocker) = exact_index_steps(&key) {
            return Fact::blocked(BTreeSet::from([blocker]));
        }
        if self.checked_access_bounds_at(path, values).is_err() {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        Fact::known(key)
    }

    fn source_path_at_site(&self, path: &AccessPath, site: NodeId) -> bool {
        let Some(node) = self.cfg.node(site) else { return false };
        let mut found = false;
        let mut visit = |candidate: &AccessPath| found |= candidate == path;
        let unresolved = &|_| false;
        if let CfgNodeKind::Evaluate(expression) = &node.kind {
            expression.visit_accesses_with(self.hir, unresolved, &mut visit);
        }
        if let CfgNodeKind::Witness { target, value } = &node.kind {
            target.visit_accesses_with(self.hir, unresolved, &mut visit);
            value.visit_accesses_with(self.hir, unresolved, &mut visit);
        }
        if let CfgNodeKind::Constraint { target, left, right } = &node.kind {
            if let Some(target) = target {
                target.visit_accesses_with(self.hir, unresolved, &mut visit);
            }
            left.visit_accesses_with(self.hir, unresolved, &mut visit);
            if let Some(right) = right {
                right.visit_accesses_with(self.hir, unresolved, &mut visit);
            }
        }
        found
    }

    pub(crate) fn exact_handle_key(&self, handle: &AccessHandle) -> Fact<AccessKey> {
        if handle.definition != self.cfg.definition() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignDefinition]));
        }
        if handle.curve != *self.field.curve() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        if let Some(evidence) = &self.evidence_binding {
            if !handle.matches_context(evidence.context()) {
                return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
            }
        }
        self.certify_access_key(handle.path(), true)
    }

    fn certify_access_key(&self, path: &AccessPath, schema_checked: bool) -> Fact<AccessKey> {
        if let Some(blocker) = self.validate_query_path(path, schema_checked) {
            return Fact::blocked(BTreeSet::from([blocker]));
        }
        if !self.scalar_storage_path(path) {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        let key = match self.resolve_access_indices(path) {
            Ok(key) => key,
            Err(blockers) => return Fact::blocked(blockers),
        };
        if self.checked_access_bounds(path).is_err() {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        Fact::known(key)
    }

    fn resolve_access_indices(
        &self,
        path: &AccessPath,
    ) -> Result<AccessKey, BTreeSet<FactBlocker>> {
        let mut key = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        for step in &mut key.steps {
            match step {
                AccessKeyStep::Index(IndexKey::Symbolic(expression)) => {
                    let fact = self.range(*expression);
                    let Some(Range::Exact(value)) = fact.certified() else {
                        return Err(fact.unavailable().cloned().unwrap_or_else(|| {
                            BTreeSet::from([FactBlocker::OpaqueExpression(*expression)])
                        }));
                    };
                    *step = AccessKeyStep::Index(IndexKey::Exact(value.clone()));
                }
                AccessKeyStep::Index(IndexKey::Unknown) => {
                    return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
                }
                AccessKeyStep::Index(IndexKey::Exact(_))
                | AccessKeyStep::Port(_)
                | AccessKeyStep::Tag(_) => {}
            }
        }
        Ok(key)
    }

    fn scalar_storage_path(&self, path: &AccessPath) -> bool {
        let Some(symbol) = self.hir.symbol(path.terminal) else { return false };
        let storage = match symbol.kind {
            SymbolKind::Variable | SymbolKind::Signal | SymbolKind::Tag => true,
            SymbolKind::Parameter | SymbolKind::Component | SymbolKind::Bus => false,
        };
        if !storage || !symbol.shape_checked || symbol.bus_type.is_some() {
            return false;
        }
        let mut indices = 0;
        for step in path.steps.iter().rev() {
            match step {
                AccessStep::Index { .. } => indices += 1,
                AccessStep::Port { .. } | AccessStep::Tag { .. } => break,
            }
        }
        indices == symbol.rank
    }
}

fn exact_index_steps(key: &AccessKey) -> Result<(), FactBlocker> {
    for step in &key.steps {
        match step {
            AccessKeyStep::Index(IndexKey::Symbolic(expression)) => {
                return Err(FactBlocker::OpaqueExpression(*expression));
            }
            AccessKeyStep::Index(IndexKey::Unknown) => {
                return Err(FactBlocker::AggregateAccess);
            }
            AccessKeyStep::Index(IndexKey::Exact(_))
            | AccessKeyStep::Port(_)
            | AccessKeyStep::Tag(_) => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::fs;

    use abstract_interpretation::graph::FlowGraph;
    use parser::hir::{lift_project, ExprKind};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::field::FieldContext;
    use crate::hir_facts::analyze_with_scalar_parameters;

    #[test]
    fn source_site_index_must_stay_within_the_specialized_dimension() {
        let directory =
            std::env::temp_dir().join(format!("circomspect-site-bound-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        fs::write(&file, "template T(n){signal output out[n];var j=1;var k=j;var i=n;out[i]<--0;}")
            .unwrap();
        let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Goldilocks);
        let n = hir.symbols().iter().find(|symbol| symbol.name == "n").unwrap().id;
        let facts = analyze_with_scalar_parameters(
            &hir,
            &cfg,
            &field,
            BTreeMap::from([(n, field.canonical(3.into()))]),
            None,
        )
        .unwrap();
        let (site, path) = cfg
            .nodes()
            .iter()
            .find_map(|site| {
                let node = cfg.node(*site)?;
                let CfgNodeKind::Witness { target, .. } = &node.kind else { return None };
                Some((*site, target))
            })
            .unwrap();
        let query = facts.exact_access_key_at(path, site);
        assert!(query.certified().is_none(), "{query:?}");
        let j = hir.symbols().iter().find(|symbol| symbol.name == "j").unwrap().id;
        let other_path = hir
            .expressions()
            .iter()
            .find_map(|expression| {
                let ExprKind::Access(path) = &expression.kind else { return None };
                (path.root == j).then_some(path)
            })
            .unwrap();
        let foreign_site = facts.exact_access_key_at(other_path, site);
        assert!(foreign_site.certified().is_none(), "{foreign_site:?}");
    }
}
