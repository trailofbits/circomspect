use num_bigint::BigInt;
use std::fmt;

use crate::ast;
use crate::environment::CircomEnvironment;
use crate::file_definition::FileLocation;

use super::value_meta::ValueKnowledge;
use super::variable_meta::VariableKnowledge;

type Index = usize;
type Version = usize;

// Trait for converting AST expressions and statements into IR.
pub type IREnvironment = CircomEnvironment<(), (), ()>;

pub trait TryIntoIR {
    type IR;
    type Error;

    fn try_into_ir(&self, env: &mut IREnvironment) -> Result<Self::IR, Self::Error>;
}

#[derive(Clone)]
pub struct Meta {
    pub elem_id: usize,
    pub start: usize,
    pub end: usize,
    pub location: FileLocation,
    pub file_id: Option<usize>,
    value_knowledge: ValueKnowledge,
    variable_knowledge: VariableKnowledge,
}

impl Meta {
    pub fn new(start: usize, end: usize) -> Meta {
        Meta {
            end,
            start,
            elem_id: 0,
            location: start..end,
            file_id: Option::None,
            value_knowledge: ValueKnowledge::default(),
            variable_knowledge: VariableKnowledge::default(),
        }
    }
    pub fn get_start(&self) -> usize {
        self.location.start
    }
    pub fn get_end(&self) -> usize {
        self.location.end
    }
    pub fn get_file_id(&self) -> usize {
        if let Option::Some(id) = self.file_id {
            id
        } else {
            panic!("Empty file id accessed")
        }
    }
    pub fn file_location(&self) -> FileLocation {
        self.location.clone()
    }
    pub fn get_value_knowledge(&self) -> &ValueKnowledge {
        &self.value_knowledge
    }
    pub fn get_variable_knowledge(&self) -> &VariableKnowledge {
        &self.variable_knowledge
    }
    pub fn get_mut_value_knowledge(&mut self) -> &mut ValueKnowledge {
        &mut self.value_knowledge
    }
    pub fn get_mut_variable_knowledge(&mut self) -> &mut VariableKnowledge {
        &mut self.variable_knowledge
    }
}

impl From<&ast::Meta> for Meta {
    fn from(meta: &ast::Meta) -> Meta {
        Meta {
            end: meta.get_end(),
            start: meta.get_start(),
            elem_id: meta.elem_id,
            location: meta.file_location(),
            file_id: meta.file_id,
            value_knowledge: ValueKnowledge::default(),
            variable_knowledge: VariableKnowledge::default(),
        }
    }
}

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
    Declaration {
        meta: Meta,
        xtype: VariableType,
        name: VariableName,
        dimensions: Vec<Expression>,
        is_constant: bool,
    },
    Substitution {
        meta: Meta,
        var: VariableName,
        access: Vec<Access>,
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

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum StatementType {
    IfThenElse,
    Return,
    Declaration,
    Substitution,
    ConstraintEquality,
    LogCall,
    Assert,
}

#[derive(Copy, Clone, PartialEq)]
pub enum SignalElementType {
    Empty,
    Binary,
    FieldElement,
}

impl From<&ast::SignalElementType> for SignalElementType {
    fn from(set: &ast::SignalElementType) -> SignalElementType {
        use ast::SignalElementType::*;
        match set {
            Empty => SignalElementType::Empty,
            Binary => SignalElementType::Binary,
            FieldElement => SignalElementType::FieldElement,
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum SignalType {
    Input,
    Output,
    Intermediate,
}

impl From<&ast::SignalType> for SignalType {
    fn from(set: &ast::SignalType) -> SignalType {
        use ast::SignalType::*;
        match set {
            Input => SignalType::Input,
            Output => SignalType::Output,
            Intermediate => SignalType::Intermediate,
        }
    }
}
/// There are only two hard things in Computer Science: cache invalidation and
/// naming things.
#[derive(Clone)]
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
    pub fn name<N: ToString>(name: N) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: None,
            version: None,
        }
    }

    /// Returns a new variable name with the given name and suffix.
    pub fn name_with_suffix<N: ToString, S: ToString>(name: N, suffix: S) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: Some(suffix.to_string()),
            version: None,
        }
    }

    /// Returns a new variable name with the given name and version.
    pub fn name_with_version<N: ToString>(name: N, version: Version) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: None,
            version: Some(version),
        }
    }

    pub fn get_name(&self) -> &String {
        &self.name
    }

    pub fn get_suffix(&self) -> &Option<String> {
        &self.suffix
    }

    pub fn get_version(&self) -> &Option<Version> {
        &self.version
    }

    /// Returns a string representing the variable (with suffix and version).
    pub fn to_string_with_version(&self) -> String {
        let mut result = self.name.clone();
        result = match self.get_suffix() {
            Some(suffix) => format!("{}_{}", result, suffix),
            None => result,
        };
        result = match self.get_version() {
            Some(version) => format!("{}.{}", result, version),
            None => result,
        };
        result
    }

    /// Returns a string representing the unversioned variable (without suffix).
    pub fn to_string_without_version(&self) -> String {
        match self.get_suffix() {
            Some(suffix) => format!("{}_{}", self.name, suffix),
            None => self.name.clone(),
        }
    }

    /// Returns a new copy of the variable name, adding the given suffix.
    pub fn with_suffix<S: ToString>(&mut self, suffix: S) -> VariableName {
        let mut result = self.clone();
        result.suffix = Some(suffix.to_string());
        result
    }

    /// Returns a new copy of the variable name, adding the given version.
    pub fn with_version(&mut self, version: Version) -> VariableName {
        let mut result = self.clone();
        result.version = Some(version);
        result
    }

    /// Returns a new copy of the variable name with the suffix dropped.
    pub fn without_suffix(&mut self) -> VariableName {
        let mut result = self.clone();
        result.suffix = None;
        result
    }

    /// Returns a new copy of the variable name with the version dropped.
    pub fn without_version(&mut self) -> VariableName {
        let mut result = self.clone();
        result.version = None;
        result
    }
}

impl From<String> for VariableName {
    fn from(name: String) -> VariableName {
        Self::from(&name)
    }
}

impl From<&String> for VariableName {
    fn from(name: &String) -> VariableName {
        // We assume that the input string uses '.' to separate the name from the suffix.
        let tokens: Vec<_> = name.split('.').collect();
        match tokens.len() {
            1 => VariableName::name(tokens[0]),
            2 => VariableName::name_with_suffix(tokens[0], tokens[1]),
            _ => panic!("invalid variable name"),
        }
    }
}

impl fmt::Display for VariableName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.to_string_with_version())
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum VariableType {
    Var,
    Component,
    Signal(SignalType, SignalElementType),
}

impl From<&ast::VariableType> for VariableType {
    fn from(set: &ast::VariableType) -> VariableType {
        use ast::VariableType::*;
        match set {
            Var => VariableType::Var,
            Component => VariableType::Component,
            Signal(st, set) => VariableType::Signal(st.into(), set.into()),
        }
    }
}

#[derive(Clone)]
pub enum Expression {
    InfixOp {
        meta: Meta,
        lhe: Box<Expression>,
        infix_op: ExpressionInfixOpcode,
        rhe: Box<Expression>,
    },
    PrefixOp {
        meta: Meta,
        prefix_op: ExpressionPrefixOpcode,
        rhe: Box<Expression>,
    },
    InlineSwitchOp {
        meta: Meta,
        cond: Box<Expression>,
        if_true: Box<Expression>,
        if_false: Box<Expression>,
    },
    Variable {
        meta: Meta,
        name: VariableName,
        access: Vec<Access>,
        version: Option<Version>,
    },
    Signal {
        meta: Meta,
        name: String,
        access: Vec<Access>,
    },
    Component {
        meta: Meta,
        name: String,
    },
    Number(Meta, BigInt),
    Call {
        meta: Meta,
        id: String,
        args: Vec<Expression>,
    },
    ArrayInLine {
        meta: Meta,
        values: Vec<Expression>,
    },
    Phi {
        meta: Meta,
        args: Vec<Expression>,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ExpressionType {
    InfixOp,
    PrefixOp,
    InlineSwitchOp,
    Variable,
    Signal,
    Component,
    Number,
    Call,
    ArrayInLine,
    Phi,
}

#[derive(Clone)]
pub enum Access {
    ArrayAccess(Expression),
    ComponentAccess(String),
}

#[derive(Copy, Clone, PartialEq)]
pub enum AssignOp {
    AssignVar,
    AssignSignal,
    AssignConstraintSignal,
}

impl From<&ast::AssignOp> for AssignOp {
    fn from(op: &ast::AssignOp) -> AssignOp {
        use ast::AssignOp::*;
        match op {
            AssignVar => AssignOp::AssignVar,
            AssignSignal => AssignOp::AssignSignal,
            AssignConstraintSignal => AssignOp::AssignConstraintSignal,
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
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

impl From<&ast::ExpressionInfixOpcode> for ExpressionInfixOpcode {
    fn from(op: &ast::ExpressionInfixOpcode) -> ExpressionInfixOpcode {
        use ast::ExpressionInfixOpcode::*;
        match op {
            Mul => ExpressionInfixOpcode::Mul,
            Div => ExpressionInfixOpcode::Div,
            Add => ExpressionInfixOpcode::Add,
            Sub => ExpressionInfixOpcode::Sub,
            Pow => ExpressionInfixOpcode::Pow,
            IntDiv => ExpressionInfixOpcode::IntDiv,
            Mod => ExpressionInfixOpcode::Mod,
            ShiftL => ExpressionInfixOpcode::ShiftL,
            ShiftR => ExpressionInfixOpcode::ShiftR,
            LesserEq => ExpressionInfixOpcode::LesserEq,
            GreaterEq => ExpressionInfixOpcode::GreaterEq,
            Lesser => ExpressionInfixOpcode::Lesser,
            Greater => ExpressionInfixOpcode::Greater,
            Eq => ExpressionInfixOpcode::Eq,
            NotEq => ExpressionInfixOpcode::NotEq,
            BoolOr => ExpressionInfixOpcode::BoolOr,
            BoolAnd => ExpressionInfixOpcode::BoolAnd,
            BitOr => ExpressionInfixOpcode::BitOr,
            BitAnd => ExpressionInfixOpcode::BitAnd,
            BitXor => ExpressionInfixOpcode::BitXor,
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum ExpressionPrefixOpcode {
    Sub,
    BoolNot,
    Complement,
}

impl From<&ast::ExpressionPrefixOpcode> for ExpressionPrefixOpcode {
    fn from(op: &ast::ExpressionPrefixOpcode) -> ExpressionPrefixOpcode {
        use ast::ExpressionPrefixOpcode::*;
        match op {
            Sub => ExpressionPrefixOpcode::Sub,
            BoolNot => ExpressionPrefixOpcode::BoolNot,
            Complement => ExpressionPrefixOpcode::Complement,
        }
    }
}
