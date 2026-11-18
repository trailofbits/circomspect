use std::collections::{BTreeMap, BTreeSet};

use crate::hir::{
    AccessPath, AccessStep, AnonymousInputEffect, AnonymousInputTarget, ArrayIndex, BlockId, Bus,
    BusId, BusTarget, CallTarget, ComponentId, ControlGuard, DefinitionKind, DefinitionRef, Effect,
    ExprId, ExprKind, HirProject, IncompleteLocation, IncompleteReason, IncompleteRegion,
    Knownness, LiftedProject, Main, PortId, PortSchema, SemanticCode, SemanticDiagnostic, Severity,
    SymbolId, SymbolKind, Template, TemplateId, ValueEvidence, Function, FunctionId,
};
use crate::frontend::{
    Access, AnonymousCallExpr, AnonymousInput, AssignmentOperator, Declaration, DeclarationKind,
    DeclaredSymbol, Definition, DefinitionKind as SourceDefinitionKind, DirectionSyntax,
    Expression, Identifier, Item, LoadedProject, LogArgument, PortDirection, Span, Statement,
    DiagnosticKind, InputAssignmentOperator, PostfixOperator,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueType {
    Plain,
    Bus(BusId),
    Component(TemplateId),
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ShapeCheck {
    Valid,
    Invalid(SemanticCode),
    Unknown,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScalarShape {
    Checked,
    Deferred,
    Invalid,
}

impl ScalarShape {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Invalid, _) | (_, Self::Invalid) => Self::Invalid,
            (Self::Deferred, _) | (_, Self::Deferred) => Self::Deferred,
            (Self::Checked, Self::Checked) => Self::Checked,
        }
    }
}

#[derive(Default)]
struct Scopes {
    stack: Vec<BTreeMap<String, SymbolId>>,
}

impl Scopes {
    fn enter(&mut self) {
        self.stack.push(BTreeMap::new());
    }
    fn leave(&mut self) {
        self.stack.pop();
    }
    fn current(&self, name: &str) -> Option<SymbolId> {
        self.stack.last().and_then(|scope| scope.get(name).copied())
    }
    fn resolve(&self, name: &str) -> Option<SymbolId> {
        self.stack.iter().rev().find_map(|scope| scope.get(name).copied())
    }
    fn outer(&self, name: &str) -> Option<SymbolId> {
        self.stack.iter().rev().skip(1).find_map(|scope| scope.get(name).copied())
    }
    fn insert(&mut self, name: String, symbol: SymbolId) {
        if let Some(scope) = self.stack.last_mut() {
            scope.insert(name, symbol);
        }
    }
}

struct AccessState {
    ty: ValueType,
    terminal: SymbolId,
    remaining_dimensions: Option<usize>,
    component_input: bool,
    component_output: bool,
    indexed_current: bool,
    steps: Vec<AccessStep>,
}

enum ResolvedField {
    Port { port: PortId, symbol: SymbolId, ty: ValueType },
    Tag { symbol: SymbolId },
}

struct TemplateInvocation<'a> {
    name: &'a Identifier,
    arguments: &'a [Expression],
    span: Span,
    parallel_span: Option<Span>,
}

#[derive(Clone, Copy)]
struct ForLoop<'a> {
    initializer: &'a Statement,
    condition: &'a Expression,
    step: &'a Statement,
    body: &'a Statement,
    span: Span,
}

impl<'a> TemplateInvocation<'a> {
    fn from_expression(expression: &'a Expression) -> Option<Self> {
        let (expression, parallel_span) = if let Expression::Parallel { operand, span } = expression
        {
            (operand.as_ref(), Some(*span))
        } else {
            (expression, None)
        };
        let Expression::Call { name, arguments, span } = expression else { return None };
        Some(Self { name, arguments, span: *span, parallel_span })
    }
}

struct Lifter<'a> {
    source: &'a LoadedProject,
    hir: HirProject,
    diagnostics: Vec<SemanticDiagnostic>,
    incomplete: Vec<IncompleteRegion>,
    expression_types: Vec<ValueType>,
    array_types: BTreeMap<(usize, usize, usize), ValueType>,
    components: BTreeMap<SymbolId, ComponentId>,
    invalid_symbols: BTreeSet<SymbolId>,
    predeclared_ports: BTreeMap<(usize, usize, usize), SymbolId>,
    definition_locations: BTreeMap<(usize, usize, usize), DefinitionRef>,
    scopes: Scopes,
    current_definition: Option<DefinitionRef>,
}

mod index;
mod statements;
mod expressions;
mod symbol_state;
mod properties;

use crate::hir::lift::symbol_state::SymbolSnapshot;

impl Lifter<'_> {
    fn diagnostic(&mut self, code: SemanticCode, severity: Severity, span: Span, message: String) {
        self.diagnostics.push(SemanticDiagnostic {
            code,
            severity,
            span,
            message,
            expected_kind: None,
            actual_kind: None,
        });
    }

    fn incomplete(&mut self, span: Span, reason: IncompleteReason) {
        self.incomplete
            .push(IncompleteRegion { location: IncompleteLocation::Source(span), reason });
    }

    fn add_expression(
        &mut self,
        kind: ExprKind,
        knownness: Knownness,
        span: Span,
        ty: ValueType,
    ) -> ExprId {
        let id = self.hir.add_expr(kind, knownness, span);
        self.expression_types.push(ty);
        id
    }

    fn expression_type(&self, id: ExprId) -> ValueType {
        self.expression_types.get(id.index).copied().unwrap_or(ValueType::Unknown)
    }

    fn knownness(&self, id: ExprId) -> Knownness {
        self.hir.expression(id).map_or(Knownness::Opaque, |expr| expr.knownness)
    }

    fn expect_compile_time(&mut self, expression: ExprId, span: Span, dimension: bool) -> bool {
        let knownness = self.knownness(expression);
        if knownness == Knownness::WitnessDependent && dimension {
            self.diagnostic(
                SemanticCode::NonConstantArrayLength,
                Severity::Error,
                span,
                "array dimension depends on a witness value".into(),
            );
        }
        if !knownness.is_compile_time() {
            self.incomplete(span, IncompleteReason::NonCompileTime);
        }
        knownness.is_compile_time()
    }

    fn resolve_pending_features(&mut self) {
        for file in &self.source.files {
            for check in &file.outcome.pending_feature_checks {
                let ty = self.array_types.get(&Self::span_key(check.span)).copied();
                match ty {
                    Some(ValueType::Bus(_)) => self.diagnostic(
                        SemanticCode::FeatureVersion,
                        Severity::Error,
                        check.span,
                        format!(
                            "bus-valued inline array requires Circom {}.{}.{}",
                            check.required_version.major,
                            check.required_version.minor,
                            check.required_version.patch
                        ),
                    ),
                    Some(ValueType::Plain) => {}
                    Some(ValueType::Component(_) | ValueType::Unknown) | None => {
                        self.incomplete(check.span, IncompleteReason::UnknownType);
                    }
                }
            }
        }
    }

    fn collect_syntax_incomplete(&mut self) {
        for diagnostic in &self.source.diagnostics {
            let reason = match diagnostic.kind {
                DiagnosticKind::MissingInclude | DiagnosticKind::FileRead => {
                    IncompleteReason::Include
                }
                _ => IncompleteReason::Syntax,
            };
            self.incomplete.push(IncompleteRegion {
                location: IncompleteLocation::from(&diagnostic.location),
                reason,
            });
        }
    }
}

/// Lifts all available definitions after indexing names across every loaded source file.
#[must_use]
pub fn lift_project(source: &LoadedProject) -> LiftedProject {
    let mut lifter = Lifter {
        source,
        hir: HirProject::new(),
        diagnostics: Vec::new(),
        incomplete: Vec::new(),
        expression_types: Vec::new(),
        array_types: BTreeMap::new(),
        components: BTreeMap::new(),
        invalid_symbols: BTreeSet::new(),
        predeclared_ports: BTreeMap::new(),
        definition_locations: BTreeMap::new(),
        scopes: Scopes::default(),
        current_definition: None,
    };
    lifter.index_definitions();
    lifter.index_parameters();
    lifter.index_ports();
    lifter.lift_definitions();
    lifter.lift_mains();
    lifter.resolve_pending_features();
    lifter.collect_syntax_incomplete();
    lifter.diagnostics.sort_by_key(|diagnostic| {
        (diagnostic.span.source().index(), diagnostic.span.start(), diagnostic.span.end())
    });
    lifter.incomplete.sort_by(|left, right| match (&left.location, &right.location) {
        (IncompleteLocation::Source(left), IncompleteLocation::Source(right)) => (
            left.source().index(),
            left.start(),
            left.end(),
        )
            .cmp(&(right.source().index(), right.start(), right.end())),
        (IncompleteLocation::Source(_), IncompleteLocation::Path(_)) => std::cmp::Ordering::Less,
        (IncompleteLocation::Path(_), IncompleteLocation::Source(_)) => std::cmp::Ordering::Greater,
        (IncompleteLocation::Path(left), IncompleteLocation::Path(right)) => left.cmp(right),
    });
    LiftedProject {
        hir: lifter.hir,
        version: source.policy.supported,
        diagnostics: lifter.diagnostics,
        syntax_diagnostics: source.diagnostics.clone(),
        incomplete: lifter.incomplete,
    }
}

#[cfg(test)]
mod property_reference;
#[cfg(test)]
mod property_tests;
