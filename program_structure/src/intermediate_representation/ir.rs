use num_bigint::BigInt;
use std::fmt;

use crate::file_definition::{FileID, FileLocation};

use super::type_meta::TypeKnowledge;
use super::value_meta::ValueKnowledge;
use super::variable_meta::VariableKnowledge;

type Index = usize;
type Version = usize;

#[derive(Clone, Default)]
pub struct Meta {
    pub location: FileLocation,
    pub file_id: Option<FileID>,
    type_knowledge: TypeKnowledge,
    value_knowledge: ValueKnowledge,
    variable_knowledge: VariableKnowledge,
}

impl Meta {
    #[must_use]
    pub fn new(location: &FileLocation, file_id: &Option<FileID>) -> Meta {
        Meta {
            location: location.clone(),
            file_id: file_id.clone(),
            type_knowledge: TypeKnowledge::default(),
            value_knowledge: ValueKnowledge::default(),
            variable_knowledge: VariableKnowledge::default(),
        }
    }

    #[must_use]
    pub fn start(&self) -> usize {
        self.location.start
    }

    #[must_use]
    pub fn end(&self) -> usize {
        self.location.end
    }

    #[must_use]
    pub fn file_id(&self) -> Option<FileID> {
        self.file_id
    }

    #[must_use]
    pub fn file_location(&self) -> FileLocation {
        self.location.clone()
    }

    #[must_use]
    pub fn type_knowledge(&self) -> &TypeKnowledge {
        &self.type_knowledge
    }

    #[must_use]
    pub fn value_knowledge(&self) -> &ValueKnowledge {
        &self.value_knowledge
    }

    #[must_use]
    pub fn variable_knowledge(&self) -> &VariableKnowledge {
        &self.variable_knowledge
    }

    #[must_use]
    pub fn type_knowledge_mut(&mut self) -> &mut TypeKnowledge {
        &mut self.type_knowledge
    }

    #[must_use]
    pub fn value_knowledge_mut(&mut self) -> &mut ValueKnowledge {
        &mut self.value_knowledge
    }

    #[must_use]
    pub fn variable_knowledge_mut(&mut self) -> &mut VariableKnowledge {
        &mut self.variable_knowledge
    }
}

impl std::hash::Hash for Meta {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.location.hash(state);
        self.file_id.hash(state);
        state.finish();
    }
}

impl PartialEq for Meta {
    fn eq(&self, other: &Meta) -> bool {
        self.location == other.location && self.file_id == other.file_id
    }
}

impl Eq for Meta {}

#[derive(Clone)]
pub enum Statement {
    IfThenElse {
        meta: Meta,
        cond: Expression,
        if_true: Index,
        if_false: Option<Index>,
    },
    Return {
        meta: Meta,
        value: Expression,
    },
    // Array and component signal assignments (where `access` is non-empty) are
    // rewritten using `Update` expressions. This allows us to track version
    // information when transforming the CFG to SSA form.
    //
    // Note: The type metadata in `meta` tracks the type of the variable `var`.
    Substitution {
        meta: Meta,
        var: VariableName,
        op: AssignOp,
        rhe: Expression,
    },
    ConstraintEquality {
        meta: Meta,
        lhe: Expression,
        rhe: Expression,
    },
    LogCall {
        meta: Meta,
        arg: Expression,
    },
    Assert {
        meta: Meta,
        arg: Expression,
    },
}

#[derive(Clone, Hash)]
pub enum Expression {
    /// An infix operation of the form `lhe * rhe`.
    InfixOp {
        meta: Meta,
        lhe: Box<Expression>,
        infix_op: ExpressionInfixOpcode,
        rhe: Box<Expression>,
    },
    /// A prefix operation of the form `* rhe`.
    PrefixOp {
        meta: Meta,
        prefix_op: ExpressionPrefixOpcode,
        rhe: Box<Expression>,
    },
    /// An inline switch operation (or inline if-then-else) of the form `cond?
    /// if_true: if_false`.
    SwitchOp {
        meta: Meta,
        cond: Box<Expression>,
        if_true: Box<Expression>,
        if_false: Box<Expression>,
    },
    /// A local variable, signal, or component.
    Variable { meta: Meta, name: VariableName },
    /// A constant field element.
    Number(Meta, BigInt),
    /// A function call node.
    Call {
        meta: Meta,
        name: String,
        args: Vec<Expression>,
    },
    /// An inline array on the form `[value, ...]`.
    Array { meta: Meta, values: Vec<Expression> },
    /// An `Access` node represents an array access of the form `a[i]...[k]`.
    Access {
        meta: Meta,
        var: VariableName,
        access: Vec<AccessType>,
    },
    /// Updates of the form `var[i]...[k] = rhe` lift to IR statements of the
    /// form `var = update(var, (i, ..., k), rhe)`. This is needed when we
    /// convert the CFG to SSA. Since arrays are versioned atomically, we need
    /// to track which version of the array that is updated to obtain the new
    /// version. (This is needed to track variable use, dead assignments, and
    /// data flow.)
    ///
    /// Note: The type metadata in `meta` tracks the type of the variable `var`.
    Update {
        meta: Meta,
        var: VariableName,
        access: Vec<AccessType>,
        rhe: Box<Expression>,
    },
    /// An SSA phi-expression.
    Phi { meta: Meta, args: Vec<VariableName> },
}

#[derive(Clone)]
pub enum VariableType {
    Local {
        dimensions: Vec<Expression>,
    },
    Component {
        dimensions: Vec<Expression>,
    },
    Signal {
        signal_type: SignalType,
        dimensions: Vec<Expression>,
    },
}

impl fmt::Display for VariableType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use VariableType::*;
        match self {
            Local { .. } => write!(f, "var"),
            Component { .. } => write!(f, "component"),
            Signal { signal_type, .. } => write!(f, "signal {signal_type}"),
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum SignalType {
    Input,
    Output,
    Intermediate,
}

impl fmt::Display for SignalType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use SignalType::*;
        match self {
            Input => write!(f, "input"),
            Output => write!(f, "output"),
            Intermediate => Ok(()), // Intermediate signals have no explicit signal type.
        }
    }
}

/// A IR variable name consists of three components.
///
///   1. The original name (obtained from the source code).
///   2. An optional suffix (used to ensure uniqueness when lifting to IR).
///   3. An optional version (applied when the CFG is converted to SSA form).
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct VariableName {
    /// This is the original name of the variable from the function or template
    /// AST.
    name: String,
    /// For shadowing declarations we need to rename the shadowing variable
    /// since construction of the CFG requires all variable names to be unique.
    /// This is done by adding a suffix (on the form `_n`) to the variable name.
    suffix: Option<String>,
    /// The version is used to track variable versions when we convert the CFG
    /// to SSA.
    version: Option<Version>,
}

impl VariableName {
    /// Returns a new variable name with the given name (without suffix or version).
    #[must_use]
    pub fn from_name<N: ToString>(name: N) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: None,
            version: None,
        }
    }

    #[must_use]
    pub fn name(&self) -> &String {
        &self.name
    }

    #[must_use]
    pub fn suffix(&self) -> &Option<String> {
        &self.suffix
    }

    #[must_use]
    pub fn version(&self) -> &Option<Version> {
        &self.version
    }

    /// Returns a new copy of the variable name, adding the given suffix.
    #[must_use]
    pub fn with_suffix<S: ToString>(&self, suffix: S) -> VariableName {
        let mut result = self.clone();
        result.suffix = Some(suffix.to_string());
        result
    }

    /// Returns a new copy of the variable name, adding the given version.
    #[must_use]
    pub fn with_version(&self, version: Version) -> VariableName {
        let mut result = self.clone();
        result.version = Some(version);
        result
    }

    /// Returns a new copy of the variable name with the suffix dropped.
    #[must_use]
    pub fn without_suffix(&self) -> VariableName {
        let mut result = self.clone();
        result.suffix = None;
        result
    }

    /// Returns a new copy of the variable name with the version dropped.
    #[must_use]
    pub fn without_version(&self) -> VariableName {
        let mut result = self.clone();
        result.version = None;
        result
    }
}

/// Display for VariableName only outputs the original name.
impl fmt::Display for VariableName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.name)
    }
}

/// Debug for VariableName outputs the full name (including suffix and version).
impl fmt::Debug for VariableName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.name)?;
        if let Some(suffix) = self.suffix() {
            write!(f, "_{suffix}")?;
        }
        if let Some(version) = self.version() {
            write!(f, ".{version}")?;
        }
        Ok(())
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub enum AccessType {
    ArrayAccess(Expression),
    ComponentAccess(String),
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum AssignOp {
    /// A signal assignment (using `<--`)
    AssignSignal,
    /// A signal assignment (using `<==`)
    AssignConstraintSignal,
    /// A local variable assignment or component initialization (using `=`).
    AssignLocalOrComponent,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum ExpressionInfixOpcode {
    Mul,
    Div,
    Add,
    Sub,
    Pow,
    IntDiv,
    Mod,
    ShiftL,
    ShiftR,
    LesserEq,
    GreaterEq,
    Lesser,
    Greater,
    Eq,
    NotEq,
    BoolOr,
    BoolAnd,
    BitOr,
    BitAnd,
    BitXor,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum ExpressionPrefixOpcode {
    Sub,
    BoolNot,
    Complement,
}
