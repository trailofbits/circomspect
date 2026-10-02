//! Schema-checked access paths that need no occurrence in the source program.

use std::collections::BTreeMap;
use std::cmp::Ordering;

use abstract_interpretation::graph::FlowGraph;
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, CallTarget, ComponentId, DefinitionRef, ExprId, ExprKind,
    PortId, PortSchema, Symbol, SymbolId, TemplateId,
};
use parser::new_frontend::PortDirection;
use program_structure::utils::constants::Curve;

use crate::hir_facts::access::{key_for_path, AccessKey};
use crate::hir_facts::field::FieldValue;
use crate::hir_facts::forward::eval_expression;
use crate::hir_facts::{AnalysisFacts, Range};
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
    #[error("the array dimension is negative or cannot be represented in this context")]
    InvalidDimension,
    #[error("the array index is outside its proved dimension")]
    IndexOutOfBounds,
}

impl AccessHandleError {
    pub(crate) fn proves_invalid_execution(self) -> bool {
        match self {
            Self::InvalidDimension | Self::IndexOutOfBounds => true,
            Self::ForeignComponent
            | Self::ForeignPort
            | Self::PortNotInTemplate
            | Self::NotOutput
            | Self::UnresolvedTarget
            | Self::NoInstantiation
            | Self::OpaquePort
            | Self::WrongRank
            | Self::UnprovedShape => false,
        }
    }
}

impl AnalysisFacts<'_> {
    /// Prove every indexed step of a source access under these bound facts.
    pub(crate) fn checked_access_bounds(&self, path: &AccessPath) -> Result<(), AccessHandleError> {
        self.checked_access_bounds_using(path, &|index| self.access_index_value(index))
    }

    pub(crate) fn checked_access_bounds_at(
        &self,
        path: &AccessPath,
        values: &BTreeMap<SymbolId, FieldValue>,
    ) -> Result<(), AccessHandleError> {
        self.checked_access_bounds_using(path, &|index| match index {
            ArrayIndex::Constant(_) => self.access_index_value(index),
            ArrayIndex::Symbolic(expression) => {
                eval_expression(self.hir, self.field, *expression, values)
                    .map(|value| value.as_bigint().clone())
                    .ok_or(AccessHandleError::UnprovedShape)
            }
        })
    }

    fn checked_access_bounds_using(
        &self,
        path: &AccessPath,
        index_value: &impl Fn(&ArrayIndex) -> Result<BigInt, AccessHandleError>,
    ) -> Result<(), AccessHandleError> {
        let mut symbol = self.hir.symbol(path.root).ok_or(AccessHandleError::UnprovedShape)?;
        let mut dimension = 0;
        for step in &path.steps {
            match step {
                AccessStep::Index { index, .. } => {
                    if !symbol.shape_checked || dimension >= symbol.rank {
                        return Err(AccessHandleError::UnprovedShape);
                    }
                    let size = *symbol
                        .dimensions
                        .get(dimension)
                        .ok_or(AccessHandleError::UnprovedShape)?;
                    let value = index_value(index)?;
                    self.check_index_bound(&value, size)?;
                    dimension += 1;
                }
                AccessStep::Port { port, .. } => {
                    if dimension != symbol.rank {
                        return Err(AccessHandleError::UnprovedShape);
                    }
                    let port = self.hir.port(*port).ok_or(AccessHandleError::UnprovedShape)?;
                    symbol =
                        self.hir.symbol(port.symbol).ok_or(AccessHandleError::UnprovedShape)?;
                    dimension = 0;
                }
                AccessStep::Tag { symbol: tag, .. } => {
                    if dimension != symbol.rank {
                        return Err(AccessHandleError::UnprovedShape);
                    }
                    symbol = self.hir.symbol(*tag).ok_or(AccessHandleError::UnprovedShape)?;
                    dimension = 0;
                }
            }
        }
        Ok(())
    }

    fn access_index_value(&self, index: &ArrayIndex) -> Result<BigInt, AccessHandleError> {
        match index {
            ArrayIndex::Constant(text) => {
                let (digits, radix) =
                    text.strip_prefix("0x").map_or((text.as_str(), 10), |hex| (hex, 16));
                BigInt::parse_bytes(digits.as_bytes(), radix)
                    .ok_or(AccessHandleError::UnprovedShape)
            }
            ArrayIndex::Symbolic(expression) => {
                let range = self.range(*expression);
                let Some(Range::Exact(value)) = range.certified() else {
                    return Err(AccessHandleError::UnprovedShape);
                };
                Ok(value.as_bigint().clone())
            }
        }
    }

    fn check_index_bound(
        &self,
        value: &BigInt,
        dimension: ExprId,
    ) -> Result<(), AccessHandleError> {
        let bound = self.dimension_bound(dimension)?;
        let index = value.to_usize().ok_or(AccessHandleError::IndexOutOfBounds)?;
        let canonical = self.field.canonical(value.clone());
        let zero = self.field.canonical(0.into());
        if index >= bound
            || canonical.as_bigint() != value
            || self.field.compare_signed(&canonical, &zero) == Ordering::Less
        {
            return Err(AccessHandleError::IndexOutOfBounds);
        }
        Ok(())
    }

    pub(crate) fn handle_relation(
        &self,
        handle: &AccessHandle,
        path: &AccessPath,
    ) -> InstanceRelation {
        let requested = key_for_path(self.hir, self.field, handle.path(), &BTreeMap::new());
        let actual = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        if requested.exact_alias(&actual) {
            InstanceRelation::Exact
        } else if requested.may_alias(&actual) {
            InstanceRelation::Possible
        } else {
            InstanceRelation::Separate
        }
    }

    pub(crate) fn instance_relation(
        &self,
        handle: &AccessHandle,
        target: &AccessPath,
    ) -> InstanceRelation {
        self.instance_path_relation(handle.path(), target)
    }

    /// Compare an already checked instantiation path with another source access.
    /// This reports aliasing only; it does not certify either input path.
    pub(crate) fn instance_path_relation(
        &self,
        instance: &AccessPath,
        target: &AccessPath,
    ) -> InstanceRelation {
        let instance = component_prefix(instance);
        let target = component_prefix(target);
        let requested = key_for_path(self.hir, self.field, &instance, &BTreeMap::new());
        let actual = key_for_path(self.hir, self.field, &target, &BTreeMap::new());
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
            context: self.evidence_binding.as_ref().map(|evidence| evidence.context().clone()),
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
            context: self.evidence_binding.as_ref().map(|evidence| evidence.context().clone()),
        })
    }

    pub(crate) fn component_bounds(
        &self,
        component: ComponentId,
    ) -> Result<Vec<usize>, AccessHandleError> {
        let component = self.hir.component(component).ok_or(AccessHandleError::ForeignComponent)?;
        self.checked_symbol_dimensions(component.symbol)
    }

    pub(crate) fn checked_symbol_dimensions(
        &self,
        symbol: SymbolId,
    ) -> Result<Vec<usize>, AccessHandleError> {
        if !self.cfg.owns_symbol(symbol) {
            return Err(AccessHandleError::UnprovedShape);
        }
        let symbol = self.hir.symbol(symbol).ok_or(AccessHandleError::UnprovedShape)?;
        if !symbol.shape_checked || symbol.dimensions.len() != symbol.rank {
            return Err(AccessHandleError::UnprovedShape);
        }
        let mut bounds = Vec::with_capacity(symbol.rank);
        let mut unproved = false;
        for dimension in &symbol.dimensions {
            match self.dimension_bound(*dimension) {
                Ok(bound) => bounds.push(bound),
                Err(error) => {
                    if error.proves_invalid_execution() {
                        return Err(error);
                    }
                    unproved = true;
                }
            }
        }
        if unproved {
            return Err(AccessHandleError::UnprovedShape);
        }
        Ok(bounds)
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
            self.check_index_bound(&BigInt::from(*index), *dimension)?;
            steps.push(AccessStep::Index {
                index: ArrayIndex::Constant(index.to_string()),
                span: symbol.span,
            });
        }
        Ok(steps)
    }

    fn dimension_bound(&self, expression: ExprId) -> Result<usize, AccessHandleError> {
        let expression = self.hir.expression(expression).ok_or(AccessHandleError::UnprovedShape)?;
        let value = if let ExprKind::Number(text) = &expression.kind {
            self.field.parse(text).ok_or(AccessHandleError::UnprovedShape)?
        } else {
            let range = self.range(expression.id);
            let Some(Range::Exact(value)) = range.certified() else {
                return Err(AccessHandleError::UnprovedShape);
            };
            value.clone()
        };
        let zero = self.field.canonical(0.into());
        if self.field.compare_signed(&value, &zero) == Ordering::Less {
            return Err(AccessHandleError::InvalidDimension);
        }
        value.as_bigint().to_usize().ok_or(AccessHandleError::InvalidDimension)
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

fn component_prefix(path: &AccessPath) -> AccessPath {
    let end = path.steps.iter().position(|step| match step {
        AccessStep::Port { .. } => true,
        AccessStep::Index { .. } | AccessStep::Tag { .. } => false,
    });
    AccessPath {
        root: path.root,
        terminal: path.root,
        steps: path.steps[..end.unwrap_or(path.steps.len())].to_vec(),
        component_input: false,
        component_output: false,
        span: path.span,
    }
}
