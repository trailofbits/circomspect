//! Checked, resolved semantic representation of an owned Circom source project.

mod lift;

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::frontend::{
    AssignmentOperator, BinaryOperator, DiagnosticLocation, InputAssignmentOperator, PortDirection,
    PostfixOperator, Span, SyntaxDiagnostic, UnaryOperator, Version,
};

pub use lift::lift_project;

static NEXT_PROJECT: AtomicU64 = AtomicU64::new(1);

/// Nonforgeable identity shared by all arena IDs in one lifted HIR project.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProjectIdentity(u64);

macro_rules! arena_id {
    ($name:ident) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name {
            index: usize,
            project: u64,
        }

        impl $name {
            const fn new(index: usize, project: u64) -> Self {
                Self { index, project }
            }
        }
    };
}

arena_id!(FunctionId);
arena_id!(TemplateId);
arena_id!(BusId);
arena_id!(SymbolId);
arena_id!(ComponentId);
arena_id!(PortId);
arena_id!(ExprId);
arena_id!(BlockId);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefinitionKind {
    Function,
    Template,
    Bus,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DefinitionRef {
    Function(FunctionId),
    Template(TemplateId),
    Bus(BusId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallTarget {
    Function(FunctionId),
    Template(TemplateId),
    Missing { expected_kind: DefinitionKind, name: String, span: Span },
    WrongKind { expected_kind: DefinitionKind, actual: DefinitionRef },
    Ambiguous { expected_kind: DefinitionKind, name: String, span: Span },
    Opaque { reason: IncompleteReason },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BusTarget {
    Bus(BusId),
    Missing { name: String, span: Span },
    WrongKind { actual: DefinitionRef, span: Span },
    Ambiguous { name: String, span: Span },
    Opaque { reason: IncompleteReason },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SymbolKind {
    Parameter,
    Variable,
    Signal,
    Component,
    Bus,
    Tag,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: String,
    pub kind: SymbolKind,
    pub span: Span,
    pub dimensions: Vec<ExprId>,
    pub rank: usize,
    pub shape_checked: bool,
    pub bus_type: Option<BusTarget>,
    pub bus_arguments: Vec<ExprId>,
    pub tags: Vec<SymbolId>,
    pub knownness: Knownness,
    pub value_evidence: ValueEvidence,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Function {
    pub id: FunctionId,
    pub name: String,
    pub parameters: Vec<SymbolId>,
    pub body: BlockId,
    pub span: Span,
    pub name_span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Template {
    pub id: TemplateId,
    pub name: String,
    pub parameters: Vec<SymbolId>,
    pub ports: Vec<PortId>,
    pub body: BlockId,
    pub custom: bool,
    pub external: bool,
    pub span: Span,
    pub name_span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Bus {
    pub id: BusId,
    pub name: String,
    pub parameters: Vec<SymbolId>,
    pub ports: Vec<PortId>,
    pub body: BlockId,
    pub span: Span,
    pub name_span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Port {
    pub id: PortId,
    pub symbol: SymbolId,
    pub direction: Option<PortDirection>,
    pub schema: PortSchema,
    pub tags: Vec<SymbolId>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PortSchema {
    Signal,
    Bus(BusId),
    Opaque(IncompleteReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Component {
    pub id: ComponentId,
    pub symbol: SymbolId,
    pub target: Option<CallTarget>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Knownness {
    Constant,
    ParameterDependent,
    WitnessDependent,
    Opaque,
}

/// Whether a variable's assigned value has a validated shape.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueEvidence {
    Checked,
    Deferred,
}

impl ValueEvidence {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Deferred, _) | (_, Self::Deferred) => Self::Deferred,
            (Self::Checked, Self::Checked) => Self::Checked,
        }
    }
}

/// Evidence available for a control-flow condition before parameter specialization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlGuard {
    CheckedCompileTime,
    DeferredScalar,
    WitnessOnly,
}

impl Knownness {
    #[must_use]
    pub const fn is_compile_time(self) -> bool {
        matches!(self, Self::Constant | Self::ParameterDependent)
    }

    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Opaque, _) | (_, Self::Opaque) => Self::Opaque,
            (Self::WitnessDependent, _) | (_, Self::WitnessDependent) => Self::WitnessDependent,
            (Self::ParameterDependent, _) | (_, Self::ParameterDependent) => {
                Self::ParameterDependent
            }
            (Self::Constant, Self::Constant) => Self::Constant,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArrayIndex {
    Constant(String),
    Symbolic(ExprId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AccessStep {
    Index { index: ArrayIndex, span: Span },
    Port { port: PortId, span: Span },
    Tag { symbol: SymbolId, span: Span },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnonymousInputTarget {
    Port(PortId),
    Opaque(IncompleteReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AnonymousInputEffect {
    pub target: AnonymousInputTarget,
    pub operator: InputAssignmentOperator,
    pub value: ExprId,
    pub span: Span,
}

impl AnonymousInputEffect {
    #[must_use]
    pub fn resolved_port(&self) -> Option<PortId> {
        match self.target {
            AnonymousInputTarget::Port(id) => Some(id),
            AnonymousInputTarget::Opaque(_) => None,
        }
    }

    #[must_use]
    pub const fn operator(&self) -> InputAssignmentOperator {
        self.operator
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AccessPath {
    pub root: SymbolId,
    pub steps: Vec<AccessStep>,
    pub terminal: SymbolId,
    pub component_input: bool,
    pub component_output: bool,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExprKind {
    Number(String),
    Access(AccessPath),
    Call {
        target: CallTarget,
        arguments: Vec<ExprId>,
    },
    AnonymousComponent {
        component: ComponentId,
        arguments: Vec<ExprId>,
        inputs: Vec<AnonymousInputEffect>,
    },
    Array(Vec<ExprId>),
    Tuple(Vec<ExprId>),
    Unary {
        operator: UnaryOperator,
        operand: ExprId,
    },
    Binary {
        operator: BinaryOperator,
        left: ExprId,
        right: ExprId,
    },
    Ternary {
        condition: ExprId,
        yes: ExprId,
        no: ExprId,
    },
    Parallel(ExprId),
    Opaque(IncompleteReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Expr {
    pub id: ExprId,
    pub kind: ExprKind,
    pub knownness: Knownness,
    pub span: Span,
}

impl Expr {
    #[must_use]
    pub fn call_target(&self) -> Option<&CallTarget> {
        match &self.kind {
            ExprKind::Call { target, .. } => Some(target),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Effect {
    Declaration {
        symbol: SymbolId,
        span: Span,
    },
    VariableAssignment {
        target: AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
        span: Span,
    },
    DeferredVariableAssignment {
        target: AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
        span: Span,
    },
    ComponentInstantiation {
        target: AccessPath,
        value: ExprId,
        span: Span,
    },
    WitnessAssignment {
        target: AccessPath,
        value: ExprId,
        span: Span,
    },
    ConstraintAssignment {
        target: AccessPath,
        value: ExprId,
        span: Span,
    },
    OpaqueAssignment {
        target: AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
        reason: IncompleteReason,
        span: Span,
    },
    EqualityConstraint {
        left: ExprId,
        right: ExprId,
        span: Span,
    },
    OpaqueEquality {
        left: ExprId,
        right: ExprId,
        reason: IncompleteReason,
        span: Span,
    },
    Update {
        target: AccessPath,
        operator: PostfixOperator,
        span: Span,
    },
    If {
        condition: ExprId,
        guard: ControlGuard,
        then_block: BlockId,
        else_block: Option<BlockId>,
        span: Span,
    },
    While {
        condition: ExprId,
        guard: ControlGuard,
        body: BlockId,
        span: Span,
    },
    For {
        initializer: BlockId,
        condition: ExprId,
        guard: ControlGuard,
        step: BlockId,
        body: BlockId,
        span: Span,
    },
    Return {
        value: ExprId,
        span: Span,
    },
    Assert {
        condition: ExprId,
        span: Span,
    },
    DeferredAssert {
        condition: ExprId,
        span: Span,
    },
    Log {
        values: Vec<ExprId>,
        span: Span,
    },
    AnonymousComponent {
        expression: ExprId,
        span: Span,
    },
    Block(BlockId),
    Opaque {
        reason: IncompleteReason,
        span: Span,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub id: BlockId,
    pub effects: Vec<Effect>,
    pub span: Span,
}

impl Block {
    #[must_use]
    pub fn expressions(&self) -> Vec<ExprId> {
        self.effects
            .iter()
            .filter_map(|effect| match effect {
                Effect::Return { value, .. }
                | Effect::AnonymousComponent { expression: value, .. } => Some(*value),
                _ => None,
            })
            .collect()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Main {
    pub target: CallTarget,
    pub arguments: Vec<ExprId>,
    pub parallel: bool,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SemanticCode {
    MissingCall,
    WrongFunction,
    WrongTemplate,
    DuplicateFunction,
    DuplicateTemplate,
    DuplicateSymbol,
    Shadowing,
    ParameterCollision,
    MissingBusType,
    InvalidAssignment,
    WrongBusAssignment,
    WrongAssignmentExpression,
    WrongAssignmentRank,
    InvalidCallArgument,
    InvalidSignalAccess,
    InvalidTag,
    InputTagAccess,
    InvalidTagAfterArray,
    InvalidArrayAccess,
    InvalidArrayIndexDimension,
    InvalidArrayIndexBus,
    AnonymousInput,
    ForbiddenDeclaration,
    TemplateReturn,
    ConstraintInFunction,
    UnknownSymbol,
    WrongArity,
    NonConstantArrayLength,
    NonComputableExpression,
    FeatureVersion,
}

impl SemanticCode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingCall => "CS0019",
            Self::WrongFunction => "T2001",
            Self::WrongTemplate => "T2002",
            Self::DuplicateFunction => "T2006",
            Self::DuplicateTemplate => "T2007",
            Self::DuplicateSymbol => "T2008",
            Self::Shadowing => "CS0001",
            Self::ParameterCollision => "CS0002",
            Self::MissingBusType => "CS0022",
            Self::InvalidAssignment => "T2000",
            Self::WrongBusAssignment => "T2059",
            Self::WrongAssignmentExpression => "T2060",
            Self::WrongAssignmentRank => "T2061",
            Self::InvalidCallArgument => "T2029",
            Self::InvalidSignalAccess => "T2046",
            Self::InvalidTag => "T2048",
            Self::InputTagAccess => "T2048-C",
            Self::InvalidTagAfterArray => "T2049",
            Self::InvalidArrayAccess => "T2032",
            Self::InvalidArrayIndexDimension => "T2033",
            Self::InvalidArrayIndexBus => "T2053",
            Self::AnonymousInput => "TAC01",
            Self::ForbiddenDeclaration => "T2016",
            Self::TemplateReturn => "T2024",
            Self::ConstraintInFunction => "T2039",
            Self::UnknownSymbol => "T2021",
            Self::WrongArity => "T20465",
            Self::NonConstantArrayLength => "T20463",
            Self::NonComputableExpression => "T20464",
            Self::FeatureVersion => "P1003",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticDiagnostic {
    pub code: SemanticCode,
    pub severity: Severity,
    pub span: Span,
    pub message: String,
    pub expected_kind: Option<DefinitionKind>,
    pub actual_kind: Option<DefinitionKind>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncompleteReason {
    Syntax,
    Include,
    MissingReference(String),
    AmbiguousReference(String),
    WrongKind(String),
    UnknownType,
    UnknownSymbol(String),
    NonCompileTime,
    InvalidAssignment,
    Unsupported(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncompleteRegion {
    pub location: IncompleteLocation,
    pub reason: IncompleteReason,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IncompleteLocation {
    Source(Span),
    Path(PathBuf),
}

impl IncompleteRegion {
    #[must_use]
    pub fn span(&self) -> Option<Span> {
        match self.location {
            IncompleteLocation::Source(span) => Some(span),
            IncompleteLocation::Path(_) => None,
        }
    }
}

impl From<&DiagnosticLocation> for IncompleteLocation {
    fn from(location: &DiagnosticLocation) -> Self {
        match location {
            DiagnosticLocation::Source(span) => Self::Source(*span),
            DiagnosticLocation::Path(path) => Self::Path(path.clone()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct LiftedProject {
    pub hir: HirProject,
    pub version: Version,
    pub diagnostics: Vec<SemanticDiagnostic>,
    pub syntax_diagnostics: Vec<SyntaxDiagnostic>,
    pub incomplete: Vec<IncompleteRegion>,
}

#[derive(Clone, Debug)]
pub struct HirProject {
    key: u64,
    functions: Vec<Function>,
    templates: Vec<Template>,
    buses: Vec<Bus>,
    symbols: Vec<Symbol>,
    components: Vec<Component>,
    ports: Vec<Port>,
    expressions: Vec<Expr>,
    blocks: Vec<Block>,
    definitions: BTreeMap<String, Vec<DefinitionRef>>,
    mains: Vec<Main>,
}

impl HirProject {
    #[must_use]
    pub fn identity(&self) -> ProjectIdentity {
        ProjectIdentity(self.key)
    }

    /// Read-only root instances of the lifted project.
    ///
    /// ```compile_fail
    /// use circomspect_parser::hir::HirProject;
    /// fn change(hir: &mut HirProject) { hir.mains.clear(); }
    /// ```
    #[must_use]
    pub fn mains(&self) -> &[Main] {
        &self.mains
    }

    fn new() -> Self {
        Self {
            key: NEXT_PROJECT.fetch_add(1, Ordering::Relaxed),
            functions: Vec::new(),
            templates: Vec::new(),
            buses: Vec::new(),
            symbols: Vec::new(),
            components: Vec::new(),
            ports: Vec::new(),
            expressions: Vec::new(),
            blocks: Vec::new(),
            definitions: BTreeMap::new(),
            mains: Vec::new(),
        }
    }

    #[must_use]
    pub fn functions(&self) -> &[Function] {
        &self.functions
    }
    #[must_use]
    pub fn templates(&self) -> &[Template] {
        &self.templates
    }
    #[must_use]
    pub fn buses(&self) -> &[Bus] {
        &self.buses
    }
    #[must_use]
    pub fn symbols(&self) -> &[Symbol] {
        &self.symbols
    }
    #[must_use]
    pub fn components(&self) -> &[Component] {
        &self.components
    }
    #[must_use]
    pub fn ports(&self) -> &[Port] {
        &self.ports
    }
    #[must_use]
    pub fn expressions(&self) -> &[Expr] {
        &self.expressions
    }
    #[must_use]
    pub fn blocks(&self) -> &[Block] {
        &self.blocks
    }

    /// Looks up a function only with a function ID from this project.
    ///
    /// ```compile_fail
    /// use circomspect_parser::hir::{HirProject, TemplateId};
    /// fn wrong_kind(project: &HirProject, id: TemplateId) {
    ///     let _ = project.function(id);
    /// }
    /// ```
    ///
    /// ```compile_fail
    /// use circomspect_parser::hir::FunctionId;
    /// let _forged = FunctionId { index: 0, project: 0 };
    /// ```
    #[must_use]
    pub fn function(&self, id: FunctionId) -> Option<&Function> {
        (id.project == self.key).then(|| self.functions.get(id.index)).flatten()
    }
    #[must_use]
    pub fn template(&self, id: TemplateId) -> Option<&Template> {
        (id.project == self.key).then(|| self.templates.get(id.index)).flatten()
    }
    #[must_use]
    pub fn bus(&self, id: BusId) -> Option<&Bus> {
        (id.project == self.key).then(|| self.buses.get(id.index)).flatten()
    }
    #[must_use]
    pub fn symbol(&self, id: SymbolId) -> Option<&Symbol> {
        (id.project == self.key).then(|| self.symbols.get(id.index)).flatten()
    }
    #[must_use]
    pub fn component(&self, id: ComponentId) -> Option<&Component> {
        (id.project == self.key).then(|| self.components.get(id.index)).flatten()
    }
    #[must_use]
    pub fn port(&self, id: PortId) -> Option<&Port> {
        (id.project == self.key).then(|| self.ports.get(id.index)).flatten()
    }
    #[must_use]
    pub fn expression(&self, id: ExprId) -> Option<&Expr> {
        (id.project == self.key).then(|| self.expressions.get(id.index)).flatten()
    }
    #[must_use]
    pub fn block(&self, id: BlockId) -> Option<&Block> {
        (id.project == self.key).then(|| self.blocks.get(id.index)).flatten()
    }
    #[must_use]
    pub fn definition(&self, name: &str) -> Option<DefinitionRef> {
        let definitions = self.definitions.get(name)?;
        (definitions.len() == 1).then_some(definitions[0])
    }
    #[must_use]
    pub fn definitions_named(&self, name: &str) -> &[DefinitionRef] {
        self.definitions.get(name).map_or(&[], Vec::as_slice)
    }

    fn add_block(&mut self, span: Span) -> BlockId {
        let id = BlockId::new(self.blocks.len(), self.key);
        self.blocks.push(Block { id, effects: Vec::new(), span });
        id
    }

    fn add_symbol(&mut self, name: String, kind: SymbolKind, span: Span) -> SymbolId {
        let id = SymbolId::new(self.symbols.len(), self.key);
        self.symbols.push(Symbol {
            id,
            name,
            kind,
            span,
            dimensions: Vec::new(),
            rank: 0,
            shape_checked: true,
            bus_type: None,
            bus_arguments: Vec::new(),
            tags: Vec::new(),
            knownness: match kind {
                SymbolKind::Parameter | SymbolKind::Tag => Knownness::ParameterDependent,
                SymbolKind::Signal | SymbolKind::Bus => Knownness::WitnessDependent,
                SymbolKind::Variable | SymbolKind::Component => Knownness::Opaque,
            },
            value_evidence: ValueEvidence::Checked,
        });
        id
    }

    fn add_port(
        &mut self,
        symbol: SymbolId,
        direction: Option<PortDirection>,
        schema: PortSchema,
        span: Span,
    ) -> PortId {
        let id = PortId::new(self.ports.len(), self.key);
        self.ports.push(Port { id, symbol, direction, schema, tags: Vec::new(), span });
        id
    }

    fn add_component(&mut self, symbol: SymbolId, span: Span) -> ComponentId {
        let id = ComponentId::new(self.components.len(), self.key);
        self.components.push(Component { id, symbol, target: None, span });
        id
    }

    fn add_expr(&mut self, kind: ExprKind, knownness: Knownness, span: Span) -> ExprId {
        let id = ExprId::new(self.expressions.len(), self.key);
        self.expressions.push(Expr { id, kind, knownness, span });
        id
    }
}
