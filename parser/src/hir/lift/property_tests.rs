// Test fixtures intentionally panic on invalid construction.
// Rust 1.74 requires `allow` because `expect` lint attributes are not stable there.
#![allow(clippy::allow_attributes, clippy::unwrap_used)]

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::lift::properties::{ExpressionChildren, ExpressionQuery};
use crate::hir::lift::{Lifter, ScalarShape, Scopes, ValueType};
use crate::hir::{
    AccessPath, AccessStep, AnonymousInputEffect, AnonymousInputTarget, ArrayIndex, CallTarget,
    ComponentId, DefinitionKind, DefinitionRef, ExprId, ExprKind, FunctionId, HirProject,
    IncompleteReason, Knownness, PortId, PortSchema, SymbolId, SymbolKind, Template, TemplateId,
    ValueEvidence,
};
use crate::new_frontend::{
    BinaryOperator, InputAssignmentOperator, LoadedProject, PortDirection, SourceId, Span,
    UnaryOperator, Version, VersionPolicy,
};
use proptest::prelude::*;

#[derive(Debug, Eq, PartialEq)]
struct Properties {
    checked: bool,
    rank: Option<usize>,
    scalar: ScalarShape,
    value_evidence: ValueEvidence,
    compile_time: bool,
    witness_only: bool,
}

fn actual(lifter: &Lifter<'_>, id: ExprId) -> Properties {
    let properties = lifter.expression_properties(id);
    Properties {
        checked: properties.checked,
        rank: properties.rank,
        scalar: properties.scalar,
        value_evidence: properties.value_evidence,
        compile_time: properties.compile_time,
        witness_only: properties.witness_only,
    }
}

fn reference(lifter: &Lifter<'_>, id: ExprId) -> Properties {
    Properties {
        checked: lifter.reference_expression_is_checked(id),
        rank: lifter.reference_expression_rank(id),
        scalar: lifter.reference_scalar_shape(id),
        value_evidence: if lifter.reference_deferred_value_shape(id) {
            ValueEvidence::Deferred
        } else {
            ValueEvidence::Checked
        },
        compile_time: lifter.reference_provisionally_compile_time(id),
        witness_only: lifter.reference_expression_is_witness_only(id),
    }
}

fn source() -> LoadedProject {
    LoadedProject {
        policy: VersionPolicy::new(Version::new(2, 2, 3)),
        files: Vec::new(),
        diagnostics: Vec::new(),
    }
}

fn lifter(source: &LoadedProject) -> Lifter<'_> {
    Lifter {
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
    }
}

struct Fixture<'a> {
    lifter: Lifter<'a>,
    span: Span,
    symbol: SymbolId,
    parameter: SymbolId,
    port: PortId,
    component: ComponentId,
    template: TemplateId,
}

impl<'a> Fixture<'a> {
    fn new(source: &'a LoadedProject) -> Self {
        let mut lifter = lifter(source);
        let span = Span::checked(SourceId::new(0), 0..1, "x").unwrap();
        let symbol = lifter.hir.add_symbol("x".into(), SymbolKind::Variable, span);
        let parameter = lifter.hir.add_symbol("n".into(), SymbolKind::Parameter, span);
        let output = lifter.hir.add_symbol("out".into(), SymbolKind::Signal, span);
        let port =
            lifter.hir.add_port(output, Some(PortDirection::Output), PortSchema::Signal, span);
        let template = TemplateId::new(0, lifter.hir.key);
        let body = lifter.hir.add_block(span);
        lifter.hir.templates.push(Template {
            id: template,
            name: "T".into(),
            parameters: vec![],
            ports: vec![port],
            body,
            custom: false,
            external: false,
            span,
            name_span: span,
        });
        let component = lifter.hir.add_component(symbol, span);
        lifter.hir.components[component.index].target = Some(CallTarget::Template(template));
        Self { lifter, span, symbol, parameter, port, component, template }
    }

    fn add(&mut self, kind: ExprKind) -> ExprId {
        self.lifter.add_expression(kind, Knownness::Constant, self.span, ValueType::Plain)
    }

    fn access(&self, symbol: SymbolId, steps: Vec<AccessStep>) -> ExprKind {
        ExprKind::Access(AccessPath {
            root: symbol,
            terminal: symbol,
            steps,
            component_input: false,
            component_output: false,
            span: self.span,
        })
    }

    fn anonymous(&self, value: ExprId, bound: bool) -> ExprKind {
        let target = if bound {
            AnonymousInputTarget::Port(self.port)
        } else {
            AnonymousInputTarget::Opaque(IncompleteReason::InvalidAssignment)
        };
        ExprKind::AnonymousComponent {
            component: self.component,
            arguments: vec![value],
            inputs: vec![AnonymousInputEffect {
                target,
                operator: InputAssignmentOperator::Constraint,
                value,
                span: self.span,
            }],
        }
    }

    fn targets(&self) -> [CallTarget; 6] {
        [
            CallTarget::Function(FunctionId::new(0, self.lifter.hir.key)),
            CallTarget::Template(self.template),
            CallTarget::Missing {
                expected_kind: DefinitionKind::Function,
                name: "Missing".into(),
                span: self.span,
            },
            CallTarget::WrongKind {
                expected_kind: DefinitionKind::Function,
                actual: DefinitionRef::Template(self.template),
            },
            CallTarget::Ambiguous {
                expected_kind: DefinitionKind::Function,
                name: "Ambiguous".into(),
                span: self.span,
            },
            CallTarget::Opaque { reason: IncompleteReason::UnknownType },
        ]
    }
}

#[test]
fn every_expression_variant_matches_independent_policy_references() {
    let source = source();
    let mut fixture = Fixture::new(&source);
    let number = fixture.add(ExprKind::Number("1".into()));
    let opaque = fixture.add(ExprKind::Opaque(IncompleteReason::UnknownType));
    let parameter = fixture.add(fixture.access(fixture.parameter, vec![]));
    let symbols = [fixture.symbol, fixture.parameter];
    for symbol in symbols {
        for index in [number, opaque, parameter] {
            fixture.add(fixture.access(
                symbol,
                vec![AccessStep::Index { index: ArrayIndex::Symbolic(index), span: fixture.span }],
            ));
        }
    }
    fixture.add(fixture.access(
        fixture.symbol,
        vec![
            AccessStep::Index { index: ArrayIndex::Constant("0".into()), span: fixture.span },
            AccessStep::Port { port: fixture.port, span: fixture.span },
            AccessStep::Tag { symbol: fixture.symbol, span: fixture.span },
        ],
    ));
    for target in fixture.targets() {
        fixture.add(ExprKind::Call { target, arguments: vec![number, parameter, opaque] });
    }
    for operand in [number, parameter, opaque] {
        fixture.add(ExprKind::Array(vec![operand, operand]));
        fixture.add(ExprKind::Tuple(vec![operand]));
        fixture.add(ExprKind::Unary { operator: UnaryOperator::Negate, operand });
        fixture.add(ExprKind::Binary {
            operator: BinaryOperator::Add,
            left: operand,
            right: number,
        });
        fixture.add(ExprKind::Ternary { condition: opaque, yes: operand, no: operand });
        fixture.add(ExprKind::Parallel(operand));
        fixture.add(fixture.anonymous(operand, true));
        fixture.add(fixture.anonymous(operand, false));
    }
    fixture.add(ExprKind::Array(vec![]));
    for expression in &fixture.lifter.hir.expressions {
        assert_eq!(
            actual(&fixture.lifter, expression.id),
            reference(&fixture.lifter, expression.id)
        );
    }
}

#[test]
fn missing_and_foreign_ids_keep_conservative_defaults() {
    let source = source();
    let fixture = Fixture::new(&source);
    let missing = ExprId::new(42, fixture.lifter.hir.key);
    let foreign = ExprId::new(0, HirProject::new().key);
    for id in [missing, foreign] {
        assert_eq!(actual(&fixture.lifter, id), reference(&fixture.lifter, id));
        assert_eq!(
            actual(&fixture.lifter, id),
            Properties {
                checked: false,
                rank: None,
                scalar: ScalarShape::Invalid,
                value_evidence: ValueEvidence::Checked,
                compile_time: false,
                witness_only: false,
            }
        );
    }
}

#[test]
fn queries_observe_changed_symbol_evidence_and_invalidated_old_expressions() {
    let source = source();
    let mut fixture = Fixture::new(&source);
    let access = fixture.add(fixture.access(fixture.symbol, vec![]));
    assert_eq!(actual(&fixture.lifter, access).scalar, ScalarShape::Checked);
    fixture.lifter.hir.symbols[fixture.symbol.index].value_evidence = ValueEvidence::Deferred;
    fixture.lifter.hir.symbols[fixture.symbol.index].knownness = Knownness::WitnessDependent;
    let changed = actual(&fixture.lifter, access);
    assert_eq!(changed.scalar, ScalarShape::Deferred);
    assert_eq!(changed.value_evidence, ValueEvidence::Deferred);
    assert!(changed.compile_time, "access retains recorded knownness");
    fixture.lifter.hir.expressions[access.index].kind =
        ExprKind::Opaque(IncompleteReason::InvalidAssignment);
    fixture.lifter.expression_types[access.index] = ValueType::Unknown;
    assert_eq!(actual(&fixture.lifter, access).scalar, ScalarShape::Invalid);
    assert!(!actual(&fixture.lifter, access).checked);
}

#[derive(Clone, Copy)]
enum Form {
    Number,
    Access,
    Call,
    Anonymous,
    Array,
    Tuple,
    Unary,
    Binary,
    Ternary,
    Parallel,
    Opaque,
}

impl Fixture<'_> {
    fn mixed_kind(&self, form: Form, [left, right, third]: [ExprId; 3]) -> ExprKind {
        match form {
            Form::Number => ExprKind::Number("2".into()),
            Form::Access => self.access(
                self.symbol,
                vec![AccessStep::Index { index: ArrayIndex::Symbolic(left), span: self.span }],
            ),
            Form::Call => ExprKind::Call {
                target: CallTarget::Function(FunctionId::new(0, self.lifter.hir.key)),
                arguments: vec![left, right],
            },
            Form::Anonymous => self.anonymous(left, true),
            Form::Array => ExprKind::Array(vec![left, right]),
            Form::Tuple => ExprKind::Tuple(vec![left, right]),
            Form::Unary => ExprKind::Unary { operator: UnaryOperator::Negate, operand: left },
            Form::Binary => ExprKind::Binary { operator: BinaryOperator::Add, left, right },
            Form::Ternary => ExprKind::Ternary { condition: left, yes: right, no: third },
            Form::Parallel => ExprKind::Parallel(left),
            Form::Opaque => ExprKind::Opaque(IncompleteReason::UnknownType),
        }
    }
}

proptest! {
    #[test]
    fn mixed_shared_graphs_match_each_recursive_policy(
        nodes in proptest::collection::vec((any::<u8>(), any::<u8>(), any::<u8>()), 0..20),
        deferred in any::<bool>(),
    ) {
        let source = source();
        let mut fixture = Fixture::new(&source);
        if deferred {
            let symbol = &mut fixture.lifter.hir.symbols[fixture.symbol.index];
            symbol.value_evidence = ValueEvidence::Deferred;
        }
        let mut ids = vec![
            fixture.add(ExprKind::Number("1".into())),
            fixture.add(ExprKind::Opaque(IncompleteReason::UnknownType)),
            fixture.add(fixture.access(fixture.parameter, vec![])),
        ];
        let forms = [
            Form::Number, Form::Access, Form::Call, Form::Anonymous, Form::Array, Form::Tuple,
            Form::Unary, Form::Binary, Form::Ternary, Form::Parallel, Form::Opaque,
        ];
        for (form, left, right) in nodes {
            let form = forms[usize::from(form) % forms.len()];
            let children = [ids[usize::from(left) % ids.len()], ids[usize::from(right) % ids.len()],
                ids[ids.len() - 1]];
            let id = fixture.add(fixture.mixed_kind(form, children));
            prop_assert_eq!(actual(&fixture.lifter, id), reference(&fixture.lifter, id));
            ids.push(id);
        }
    }
}

#[test]
fn expression_policies_keep_distinct_admission_rules() {
    let source = source();
    let mut fixture = Fixture::new(&source);
    let number = fixture.add(ExprKind::Number("1".into()));
    let opaque = fixture.add(ExprKind::Opaque(IncompleteReason::UnknownType));
    let unary = fixture.add(ExprKind::Unary { operator: UnaryOperator::Negate, operand: opaque });
    assert_eq!(actual(&fixture.lifter, unary).rank, Some(0));
    assert!(!actual(&fixture.lifter, unary).checked);
    let ternary = fixture.add(ExprKind::Ternary { condition: opaque, yes: number, no: number });
    assert_eq!(actual(&fixture.lifter, ternary).rank, Some(0));
    assert_eq!(actual(&fixture.lifter, ternary).scalar, ScalarShape::Invalid);
    let function = fixture.add(ExprKind::Call {
        target: CallTarget::Function(FunctionId::new(0, fixture.lifter.hir.key)),
        arguments: vec![],
    });
    let call = actual(&fixture.lifter, function);
    assert_eq!(call.scalar, ScalarShape::Deferred);
    assert!(call.checked && call.value_evidence == ValueEvidence::Deferred && call.compile_time);
    assert!(!call.witness_only);
    let parallel = fixture.add(ExprKind::Parallel(number));
    assert_eq!(actual(&fixture.lifter, parallel).scalar, ScalarShape::Checked);
    fixture.lifter.expression_types[parallel.index] = ValueType::Unknown;
    assert_eq!(actual(&fixture.lifter, parallel).scalar, ScalarShape::Invalid);
    let indexed = fixture.add(fixture.access(
        fixture.symbol,
        vec![AccessStep::Index { index: ArrayIndex::Symbolic(opaque), span: fixture.span }],
    ));
    assert!(!actual(&fixture.lifter, indexed).checked);
    let mut anonymous = fixture.anonymous(number, true);
    if let ExprKind::AnonymousComponent { inputs, .. } = &mut anonymous {
        inputs[0].value = opaque;
    }
    let anonymous = fixture.add(anonymous);
    assert!(!actual(&fixture.lifter, anonymous).checked);
}

#[test]
fn direct_children_preserve_source_order_and_duplicate_occurrences() {
    let source = source();
    let mut fixture = Fixture::new(&source);
    let a = fixture.add(ExprKind::Number("1".into()));
    let b = fixture.add(ExprKind::Number("2".into()));
    let c = fixture.add(ExprKind::Number("3".into()));
    for (form, expected) in [
        (Form::Number, vec![]),
        (Form::Access, vec![a]),
        (Form::Call, vec![a, b]),
        (Form::Anonymous, vec![a, a]),
        (Form::Array, vec![a, b]),
        (Form::Tuple, vec![a, b]),
        (Form::Unary, vec![a]),
        (Form::Binary, vec![a, b]),
        (Form::Ternary, vec![a, b, c]),
        (Form::Parallel, vec![a]),
        (Form::Opaque, vec![]),
    ] {
        let kind = fixture.mixed_kind(form, [a, b, c]);
        let mut children = Vec::new();
        kind.for_each_child(|id| children.push(id));
        assert_eq!(children, expected);
    }
    let kind = fixture.access(
        fixture.symbol,
        vec![
            AccessStep::Index { index: ArrayIndex::Symbolic(c), span: fixture.span },
            AccessStep::Index { index: ArrayIndex::Constant("0".into()), span: fixture.span },
            AccessStep::Port { port: fixture.port, span: fixture.span },
            AccessStep::Tag { symbol: fixture.symbol, span: fixture.span },
            AccessStep::Index { index: ArrayIndex::Symbolic(a), span: fixture.span },
        ],
    );
    let mut children = Vec::new();
    kind.for_each_child(|id| children.push(id));
    assert_eq!(children, [c, a]);
}

#[test]
fn deep_shared_graph_queries_complete_each_node_once() {
    let source = source();
    let mut fixture = Fixture::new(&source);
    let mut root = fixture.add(ExprKind::Number("1".into()));
    let depth = 20_000;
    for _ in 0..depth {
        root = fixture.add(ExprKind::Binary {
            operator: BinaryOperator::Add,
            left: root,
            right: root,
        });
    }
    let mut query = ExpressionQuery::new(&fixture.lifter);
    let result = query.get(root);
    assert!(result.checked && result.compile_time && result.witness_only);
    assert_eq!(result.scalar, ScalarShape::Checked);
    assert_eq!(query.completed_nodes(), depth + 1);
    assert_eq!(query.child_visits, 2 * depth);
    assert_eq!(query.get(root), result);
    assert_eq!(query.child_visits, 2 * depth);
}

#[test]
fn cached_local_properties_never_match_a_foreign_project_id() {
    let source = source();
    let mut fixture = Fixture::new(&source);
    let local = fixture.add(ExprKind::Number("1".into()));
    let foreign = ExprId::new(local.index, HirProject::new().key);
    let mut query = ExpressionQuery::new(&fixture.lifter);
    assert!(query.get(local).checked);
    assert!(!query.get(foreign).checked);
    assert_eq!(query.completed_nodes(), 2);
    let parent = fixture.add(ExprKind::Binary {
        operator: BinaryOperator::Add,
        left: local,
        right: foreign,
    });
    assert_eq!(actual(&fixture.lifter, parent), reference(&fixture.lifter, parent));
    assert!(!actual(&fixture.lifter, parent).checked);
    assert_eq!(actual(&fixture.lifter, parent).rank, Some(0));
}
