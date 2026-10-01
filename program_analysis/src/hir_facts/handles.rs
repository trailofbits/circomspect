//! Schema-checked access paths that need no occurrence in the source program.

use std::collections::BTreeMap;
use std::cmp::Ordering;

use abstract_interpretation::graph::FlowGraph;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, CallTarget, ComponentId, DefinitionRef, ExprId, ExprKind,
    PortId, PortSchema, Symbol, TemplateId,
};
use parser::new_frontend::PortDirection;
use program_structure::utils::constants::Curve;

use super::access::{key_for_path, AccessKey};
use super::{AnalysisFacts, Range};
use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::interprocedural::CallContext;

/// A checked port access. Its source path cannot be assembled by callers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AccessHandle {
    pub(super) definition: DefinitionRef,
    pub(super) curve: Curve,
    pub(super) path: AccessPath,
    component: Option<ComponentId>,
    context: Option<CallContext>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InstanceRelation {
    Exact,
    Possible,
    Separate,
}

impl AccessHandle {
    #[must_use]
    pub fn component(&self) -> Option<ComponentId> {
        self.component
    }

    #[must_use]
    pub fn span(&self) -> parser::new_frontend::Span {
        self.path.span
    }

    pub(crate) fn path(&self) -> &AccessPath {
        &self.path
    }

    pub(crate) fn matches_context(&self, context: &CallContext) -> bool {
        self.context.as_ref() == Some(context)
    }

    pub(crate) fn output_port(&self) -> Option<(PortId, Vec<usize>)> {
        self.component?;
        let mut steps = self.path.steps.iter();
        let port = steps.find_map(|step| match step {
            AccessStep::Port { port, .. } => Some(*port),
            AccessStep::Index { .. } | AccessStep::Tag { .. } => None,
        })?;
        let mut indices = Vec::new();
        for step in steps {
            let AccessStep::Index { index: ArrayIndex::Constant(value), .. } = step else {
                return None;
            };
            indices.push(value.parse().ok()?);
        }
        Some((port, indices))
    }
}

/// Why a declared port cannot be named as an exact checked access.
#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum AccessHandleError {
    #[error("the component is outside the analyzed definition")]
    ForeignComponent,
    #[error("the port is outside the analyzed definition")]
    ForeignPort,
    #[error("the port does not belong to the component template")]
    PortNotInTemplate,
    #[error("the component port is not an output")]
    NotOutput,
    #[error("the component template cannot be resolved")]
    UnresolvedTarget,
    #[error("the component has no checked instantiation")]
    NoInstantiation,
    #[error("the port schema is incomplete")]
    OpaquePort,
    #[error("the number of array indices does not match the declared rank")]
    WrongRank,
    #[error("the array dimension is not proved in this context")]
    UnprovedShape,
    #[error("the array index is outside its proved dimension")]
    IndexOutOfBounds,
}

impl AnalysisFacts<'_> {
    pub(crate) fn instance_relation(
        &self,
        handle: &AccessHandle,
        target: &AccessPath,
    ) -> InstanceRelation {
        let Some(port_position) = handle.path.steps.iter().position(|step| match step {
            AccessStep::Port { .. } => true,
            AccessStep::Index { .. } | AccessStep::Tag { .. } => false,
        }) else {
            return InstanceRelation::Possible;
        };
        let instance = AccessPath {
            root: handle.path.root,
            steps: handle.path.steps[..port_position].to_vec(),
            terminal: handle.path.root,
            component_input: false,
            component_output: false,
            span: handle.path.span,
        };
        let requested = key_for_path(self.hir, self.field, &instance, &BTreeMap::new());
        let actual = key_for_path(self.hir, self.field, target, &BTreeMap::new());
        if requested.exact_alias(&actual) {
            InstanceRelation::Exact
        } else if requested.may_alias(&actual) {
            InstanceRelation::Possible
        } else {
            InstanceRelation::Separate
        }
    }

    /// Name a declared local template or bus port, even with no source occurrence.
    pub fn port_handle(
        &self,
        port: PortId,
        indices: &[usize],
    ) -> Result<AccessHandle, AccessHandleError> {
        let ports = match self.cfg.definition() {
            DefinitionRef::Function(_) => &[][..],
            DefinitionRef::Template(id) => {
                &self.hir.template(id).ok_or(AccessHandleError::ForeignPort)?.ports
            }
            DefinitionRef::Bus(id) => {
                &self.hir.bus(id).ok_or(AccessHandleError::ForeignPort)?.ports
            }
        };
        if !ports.contains(&port) {
            return Err(AccessHandleError::ForeignPort);
        }
        let port = self.hir.port(port).ok_or(AccessHandleError::ForeignPort)?;
        if let PortSchema::Opaque(_) = port.schema {
            return Err(AccessHandleError::OpaquePort);
        }
        let symbol = self.hir.symbol(port.symbol).ok_or(AccessHandleError::ForeignPort)?;
        if !self.cfg.owns_symbol(symbol.id) {
            return Err(AccessHandleError::ForeignPort);
        }
        let path = AccessPath {
            root: symbol.id,
            steps: self.checked_indices(symbol, indices)?,
            terminal: symbol.id,
            component_input: false,
            component_output: false,
            span: port.span,
        };
        Ok(AccessHandle {
            definition: self.cfg.definition(),
            curve: self.field.curve().clone(),
            path,
            component: None,
            context: self.context_binding.clone(),
        })
    }

    /// Name an exact output of a resolved component instance without a source access.
    pub fn component_output_handle(
        &self,
        component: ComponentId,
        component_indices: &[usize],
        port: PortId,
        port_indices: &[usize],
    ) -> Result<AccessHandle, AccessHandleError> {
        let component = self.hir.component(component).ok_or(AccessHandleError::ForeignComponent)?;
        if !self.cfg.owns_symbol(component.symbol) {
            return Err(AccessHandleError::ForeignComponent);
        }
        let Some(CallTarget::Template(template)) = component.target else {
            return Err(AccessHandleError::UnresolvedTarget);
        };
        let template = self.hir.template(template).ok_or(AccessHandleError::UnresolvedTarget)?;
        if !template.ports.contains(&port) {
            return Err(AccessHandleError::PortNotInTemplate);
        }
        let port = self.hir.port(port).ok_or(AccessHandleError::PortNotInTemplate)?;
        if port.direction != Some(PortDirection::Output) {
            return Err(AccessHandleError::NotOutput);
        }
        if let PortSchema::Opaque(_) = port.schema {
            return Err(AccessHandleError::OpaquePort);
        }
        let root = self.hir.symbol(component.symbol).ok_or(AccessHandleError::ForeignComponent)?;
        let terminal = self.hir.symbol(port.symbol).ok_or(AccessHandleError::PortNotInTemplate)?;
        let mut steps = self.checked_indices(root, component_indices)?;
        self.check_instantiations(component.symbol, &steps, template.id)?;
        steps.push(AccessStep::Port { port: port.id, span: port.span });
        steps.extend(self.checked_indices(terminal, port_indices)?);
        let path = AccessPath {
            root: root.id,
            steps,
            terminal: terminal.id,
            component_input: false,
            component_output: true,
            span: component.span,
        };
        Ok(AccessHandle {
            definition: self.cfg.definition(),
            curve: self.field.curve().clone(),
            path,
            component: Some(component.id),
            context: self.context_binding.clone(),
        })
    }

    fn checked_indices(
        &self,
        symbol: &Symbol,
        indices: &[usize],
    ) -> Result<Vec<AccessStep>, AccessHandleError> {
        if indices.len() != symbol.rank {
            return Err(AccessHandleError::WrongRank);
        }
        if symbol.rank > 0 && !symbol.shape_checked {
            return Err(AccessHandleError::UnprovedShape);
        }
        let mut steps = Vec::with_capacity(indices.len());
        for (dimension, index) in symbol.dimensions.iter().zip(indices) {
            let bound = self.dimension_bound(*dimension)?;
            let literal = BigInt::from(*index);
            if *index >= bound || self.field.canonical(literal.clone()).as_bigint() != &literal {
                return Err(AccessHandleError::IndexOutOfBounds);
            }
            steps.push(AccessStep::Index {
                index: ArrayIndex::Constant(index.to_string()),
                span: symbol.span,
            });
        }
        Ok(steps)
    }

    fn dimension_bound(&self, expression: ExprId) -> Result<usize, AccessHandleError> {
        let expression = self.hir.expression(expression).ok_or(AccessHandleError::UnprovedShape)?;
        if let ExprKind::Number(text) = &expression.kind {
            let (digits, radix) = if let Some(hex) = text.strip_prefix("0x") {
                (hex, 16)
            } else {
                (text.as_str(), 10)
            };
            return BigInt::parse_bytes(digits.as_bytes(), radix)
                .and_then(|value| value.to_usize())
                .ok_or(AccessHandleError::UnprovedShape);
        }
        let range = self.range(expression.id);
        let Some(Range::Exact(value)) = range.certified() else {
            return Err(AccessHandleError::UnprovedShape);
        };
        let zero = self.field.canonical(0.into());
        if self.field.compare_signed(value, &zero) == Ordering::Less {
            return Err(AccessHandleError::UnprovedShape);
        }
        value.as_bigint().to_usize().ok_or(AccessHandleError::UnprovedShape)
    }

    fn check_instantiations(
        &self,
        symbol: parser::hir::SymbolId,
        indices: &[AccessStep],
        template: TemplateId,
    ) -> Result<(), AccessHandleError> {
        let requested = AccessPath {
            root: symbol,
            steps: indices.to_vec(),
            terminal: symbol,
            component_input: false,
            component_output: false,
            span: self.hir.symbol(symbol).ok_or(AccessHandleError::ForeignComponent)?.span,
        };
        let key = key_for_path(self.hir, self.field, &requested, &BTreeMap::new());
        let mut found = false;
        for id in self.cfg.nodes() {
            let Some(node) = self.cfg.node(*id) else { continue };
            let Some(actual) = self.instance_target(node, symbol, &key)? else {
                continue;
            };
            found = true;
            if actual != template {
                return Err(AccessHandleError::UnresolvedTarget);
            }
        }
        if found {
            Ok(())
        } else {
            Err(AccessHandleError::NoInstantiation)
        }
    }

    fn instance_target(
        &self,
        node: &CfgNode,
        symbol: parser::hir::SymbolId,
        requested: &AccessKey,
    ) -> Result<Option<TemplateId>, AccessHandleError> {
        if let CfgNodeKind::OpaqueAssignment { target, .. } = &node.kind {
            if target.root == symbol {
                return Err(AccessHandleError::UnresolvedTarget);
            }
        }
        let CfgNodeKind::Instantiate { target, value } = &node.kind else {
            return Ok(None);
        };
        if target.root != symbol {
            return Ok(None);
        }
        let other = key_for_path(self.hir, self.field, target, &BTreeMap::new());
        if !requested.may_alias(&other) {
            return Ok(None);
        }
        self.template_of_expression(*value).map(Some).ok_or(AccessHandleError::UnresolvedTarget)
    }

    fn template_of_expression(&self, value: ExprId) -> Option<TemplateId> {
        let value = self.hir.expression(value)?;
        if let ExprKind::Parallel(inner) = value.kind {
            return self.template_of_expression(inner);
        }
        if let ExprKind::Call { target: CallTarget::Template(id), .. } = value.kind {
            Some(id)
        } else {
            None
        }
    }
}
