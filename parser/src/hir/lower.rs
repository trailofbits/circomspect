use std::collections::{BTreeMap, BTreeSet};

use super::{
    AccessPath, AccessStep, AnonymousInputEffect, AnonymousInputTarget, ArrayIndex, BlockId, Bus,
    BusId, BusTarget, CallTarget, ComponentId, DefinitionKind, DefinitionRef, Effect, ExprId,
    ExprKind, HirProject, IncompleteLocation, IncompleteReason, IncompleteRegion, Knownness,
    LoweredProject, Main, PortSchema, SemanticCode, SemanticDiagnostic, Severity, SymbolId,
    SymbolKind, Template, TemplateId, Function, FunctionId,
};
use crate::new_frontend::{
    Access, AnonymousCallExpr, AnonymousInput, AssignmentOperator, Declaration, DeclarationKind,
    DeclaredSymbol, Definition, DefinitionKind as SourceDefinitionKind, DirectionSyntax,
    Expression, Identifier, Item, LoadedProject, LogArgument, PortDirection, Span, Statement,
    DiagnosticKind, InputAssignmentOperator,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueType {
    Plain,
    Bus(BusId),
    Component(TemplateId),
    Unknown,
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
    remaining_dimensions: usize,
    component_input: bool,
    component_output: bool,
    indexed_current: bool,
    steps: Vec<AccessStep>,
}

struct Lowerer<'a> {
    source: &'a LoadedProject,
    hir: HirProject,
    diagnostics: Vec<SemanticDiagnostic>,
    incomplete: Vec<IncompleteRegion>,
    expression_types: Vec<ValueType>,
    array_types: BTreeMap<(usize, usize, usize), ValueType>,
    components: BTreeMap<SymbolId, ComponentId>,
    predeclared_ports: BTreeMap<(usize, usize, usize), SymbolId>,
    definition_locations: BTreeMap<(usize, usize, usize), DefinitionRef>,
    scopes: Scopes,
    current_definition: Option<DefinitionRef>,
}

mod index;
mod statements;
mod expressions;

impl Lowerer<'_> {
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
                    Some(ValueType::Component(_)) | Some(ValueType::Unknown) | None => {
                        self.incomplete(check.span, IncompleteReason::UnknownType);
                    }
                }
            }
        }
    }

    fn collect_syntax_incomplete(&mut self) {
        for diagnostic in &self.source.diagnostics {
            let reason = match diagnostic.kind {
                DiagnosticKind::MissingInclude
                | DiagnosticKind::FileRead
                | DiagnosticKind::CyclicInclude => IncompleteReason::Include,
                _ => IncompleteReason::Syntax,
            };
            self.incomplete.push(IncompleteRegion {
                location: IncompleteLocation::from(&diagnostic.location),
                reason,
            });
        }
    }
}

/// Lowers all available definitions after indexing names across every loaded source file.
#[must_use]
pub fn lower_project(source: &LoadedProject) -> LoweredProject {
    let mut lowerer = Lowerer {
        source,
        hir: HirProject::new(),
        diagnostics: Vec::new(),
        incomplete: Vec::new(),
        expression_types: Vec::new(),
        array_types: BTreeMap::new(),
        components: BTreeMap::new(),
        predeclared_ports: BTreeMap::new(),
        definition_locations: BTreeMap::new(),
        scopes: Scopes::default(),
        current_definition: None,
    };
    lowerer.index_definitions();
    lowerer.index_parameters();
    lowerer.index_ports();
    lowerer.lower_definitions();
    lowerer.lower_mains();
    lowerer.resolve_pending_features();
    lowerer.collect_syntax_incomplete();
    lowerer.diagnostics.sort_by_key(|diagnostic| {
        (diagnostic.span.source().index(), diagnostic.span.start(), diagnostic.span.end())
    });
    lowerer.incomplete.sort_by(|left, right| match (&left.location, &right.location) {
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
    LoweredProject {
        hir: lowerer.hir,
        diagnostics: lowerer.diagnostics,
        syntax_diagnostics: source.diagnostics.clone(),
        incomplete: lowerer.incomplete,
    }
}
