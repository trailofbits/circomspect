use num_bigint::BigInt;
use std::collections::HashSet;
use std::fmt;

use crate::ast;
use crate::environment::VarEnvironment;
use crate::file_definition::{FileID, FileLocation};

use super::declaration_map::Declaration;
use super::value_meta::ValueKnowledge;
use super::variable_meta::VariableKnowledge;

type Index = usize;
type Version = usize;
type VariableSet = HashSet<String>;

pub struct IREnvironment {
    scoped_declarations: VarEnvironment<Declaration>,
    global_declarations: VarEnvironment<Declaration>,
    variables: VariableSet,
}

impl IREnvironment {
    #[must_use]
    pub fn new() -> IREnvironment {
        IREnvironment {
            scoped_declarations: VarEnvironment::new(),
            global_declarations: VarEnvironment::new(),
            variables: VariableSet::new(),
        }
    }

    pub fn add_declaration(&mut self, name: &str, declaration: Declaration) {
        self.variables.insert(name.to_string());
        self.scoped_declarations
            .add_variable(name, declaration.clone());
        self.global_declarations.add_variable(name, declaration);
    }

    #[must_use]
    pub fn get_declaration(&mut self, name: &str) -> Option<&Declaration> {
        self.scoped_declarations.get_variable(name)
    }

    // Enter variable scope.
    pub fn add_variable_block(&mut self) {
        self.scoped_declarations.add_variable_block();
    }

    // Leave variable scope.
    pub fn remove_variable_block(&mut self) {
        self.scoped_declarations.remove_variable_block();
    }

    pub fn iter(&self) -> impl Iterator<Item = &String> {
        self.variables.iter()
    }

    #[must_use]
    pub fn scoped_declarations(&self) -> &VarEnvironment<Declaration> {
        &self.scoped_declarations
    }

    #[must_use]
    pub fn global_declarations(&self) -> &VarEnvironment<Declaration> {
        &self.global_declarations
    }
}

pub trait TryIntoIR {
    type IR;
    type Error;

    fn try_into_ir(&self, env: &mut IREnvironment) -> Result<Self::IR, Self::Error>;
}

#[derive(Clone, Default)]
pub struct Meta {
    pub elem_id: usize,
    pub location: FileLocation,
    pub file_id: Option<FileID>,
    value_knowledge: ValueKnowledge,
    variable_knowledge: VariableKnowledge,
}

impl Meta {
    #[must_use]
    pub fn get_start(&self) -> usize {
        self.location.start
    }
    #[must_use]
    pub fn get_end(&self) -> usize {
        self.location.end
    }
    #[must_use]
    pub fn get_file_id(&self) -> Option<FileID> {
        self.file_id
    }
    #[must_use]
    pub fn file_location(&self) -> FileLocation {
        self.location.clone()
    }
    #[must_use]
    pub fn get_value_knowledge(&self) -> &ValueKnowledge {
        &self.value_knowledge
    }
    #[must_use]
    pub fn get_variable_knowledge(&self) -> &VariableKnowledge {
        &self.variable_knowledge
    }
    #[must_use]
    pub fn get_value_knowledge_mut(&mut self) -> &mut ValueKnowledge {
        &mut self.value_knowledge
    }
    #[must_use]
    pub fn get_variable_knowledge_mut(&mut self) -> &mut VariableKnowledge {
        &mut self.variable_knowledge
    }
}

impl std::hash::Hash for Meta {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.elem_id.hash(state);
        self.location.hash(state);
        self.file_id.hash(state);
        state.finish();
    }
}

impl PartialEq for Meta {
    fn eq(&self, other: &Meta) -> bool {
        self.elem_id == other.elem_id
            && self.location == other.location
            && self.file_id == other.file_id
    }
}

impl Eq for Meta {}

impl From<&ast::Meta> for Meta {
    fn from(meta: &ast::Meta) -> Meta {
        Meta {
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

#[derive(Clone, Hash, Eq, PartialEq)]
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
    },
    Signal {
        meta: Meta,
        name: VariableName,
        access: Vec<Access>,
    },
    Component {
        meta: Meta,
        name: VariableName,
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
        args: Vec<VariableName>,
    },
}

/// There are only two hard things in Computer Science: cache invalidation and
/// naming things.
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
    pub fn name<N: ToString>(name: N) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: None,
            version: None,
        }
    }

    /// Returns a new variable name with the given name and suffix.
    #[must_use]
    pub fn name_with_suffix<N: ToString, S: ToString>(name: N, suffix: S) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: Some(suffix.to_string()),
            version: None,
        }
    }

    /// Returns a new variable name with the given name and version.
    #[must_use]
    pub fn name_with_version<N: ToString>(name: N, version: Version) -> VariableName {
        VariableName {
            name: name.to_string(),
            suffix: None,
            version: Some(version),
        }
    }

    #[must_use]
    pub fn get_name(&self) -> &String {
        &self.name
    }

    #[must_use]
    pub fn get_suffix(&self) -> &Option<String> {
        &self.suffix
    }

    #[must_use]
    pub fn get_version(&self) -> &Option<Version> {
        &self.version
    }

    /// Returns a string representing the variable (with suffix and version).
    #[must_use]
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
    #[must_use]
    pub fn to_string_without_version(&self) -> String {
        match self.get_suffix() {
            Some(suffix) => format!("{}_{}", self.name, suffix),
            None => self.name.clone(),
        }
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

impl From<String> for VariableName {
    fn from(name: String) -> VariableName {
        Self::from(&name[..])
    }
}

impl From<&str> for VariableName {
    fn from(name: &str) -> VariableName {
        // We assume that the input string uses '.' to separate the name from the suffix.
        let tokens: Vec<_> = name.split('.').collect();
        match tokens.len() {
            1 => VariableName::name(tokens[0]),
            2 => VariableName::name_with_suffix(tokens[0], tokens[1]),
            _ => panic!("invalid variable name"),
        }
    }
}

impl fmt::Debug for VariableName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.to_string_with_version())
    }
}

impl fmt::Display for VariableName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.to_string_with_version())
    }
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

#[derive(Clone, Hash, Eq, PartialEq)]
pub enum Access {
    ArrayAccess(Expression),
    ComponentAccess(String),
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
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

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
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

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn variable_name_from_string(name in "[$_]*[a-zA-Z][a-zA-Z$_0-9]*") {
            use super::VariableName;
            let var = VariableName::from(name);
            assert!(var.get_suffix().is_none());
            assert!(var.get_version().is_none());
        }
    }
}
