use std::collections::HashMap;
use std::fmt;
use std::fmt::{Display, Formatter};

use crate::ast;
use crate::file_definition::{FileID, FileLocation};
use crate::ir::errors::{IRError, IRResult};
use crate::ir::*;

// All variable types are tracked by the declaration map. (Since all versions of
// the same variable have the same type, they are represented internally using
// the unversioned variable name.)
#[derive(Clone)]
pub struct DeclarationMap {
    declarations: HashMap<VariableName, Declaration>,
}

impl DeclarationMap {
    #[must_use]
    pub fn new() -> DeclarationMap {
        DeclarationMap {
            declarations: HashMap::new(),
        }
    }

    pub fn add_declaration(&mut self, name: &VariableName, declaration: Declaration) {
        assert!(
            self.declarations
                .insert(name.clone(), declaration)
                .is_none(),
            "variable `{}` already tracked by declaration map",
            name
        );
    }

    #[must_use]
    pub fn get_declaration(&self, name: &VariableName) -> Option<&Declaration> {
        self.declarations.get(&name.without_version())
    }

    #[must_use]
    pub fn get_type(&self, name: &VariableName) -> Option<&VariableType> {
        self.get_declaration(name)
            .map(|declararation| declararation.get_type())
    }

    #[must_use]
    pub fn get_dimensions(&self, name: &VariableName) -> Option<&Vec<Expression>> {
        self.get_declaration(name)
            .map(|declararation| declararation.get_dimensions())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&VariableName, &Declaration)> {
        self.declarations.iter()
    }
}

/// To avoid having to add a new declaration for each new version of a variable
/// we track all declarations as part of the CFG header.
#[derive(Clone)]
pub struct Declaration {
    name: VariableName,
    xtype: VariableType,
    dimensions: Vec<Expression>,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl Declaration {
    pub fn new(
        name: &VariableName,
        xtype: &VariableType,
        dimensions: &Vec<Expression>,
        file_id: Option<FileID>,
        file_location: &FileLocation,
    ) -> Declaration {
        Declaration {
            name: name.clone(),
            xtype: xtype.clone(),
            dimensions: dimensions.clone(),
            file_id: file_id.clone(),
            file_location: file_location.clone(),
        }
    }

    #[must_use]
    pub fn get_file_id(&self) -> Option<FileID> {
        self.file_id
    }

    #[must_use]
    pub fn get_location(&self) -> FileLocation {
        self.file_location.clone()
    }

    #[must_use]
    pub fn get_name(&self) -> &VariableName {
        &self.name
    }

    #[must_use]
    pub fn get_type(&self) -> &VariableType {
        &self.xtype
    }

    #[must_use]
    pub fn get_dimensions(&self) -> &Vec<Expression> {
        &self.dimensions
    }
}

impl TryIntoIR for (ast::Meta, String, ast::VariableType, Vec<ast::Expression>) {
    type IR = Declaration;
    type Error = IRError;

    fn try_into_ir(&self, env: &mut IREnvironment) -> IRResult<Declaration> {
        let (meta, name, xtype, dimensions) = self;
        Ok(Declaration {
            name: name[..].into(),
            xtype: xtype.into(),
            dimensions: dimensions
                .iter()
                .map(|xt| xt.try_into_ir(env))
                .collect::<IRResult<Vec<Expression>>>()?,
            file_id: meta.file_id,
            file_location: meta.file_location(),
        })
    }
}

impl From<&IREnvironment> for DeclarationMap {
    fn from(env: &IREnvironment) -> DeclarationMap {
        let mut declarations = DeclarationMap::new();
        for name in env.iter() {
            let declaration = env
                .global_declarations()
                .get_variable(name)
                .expect("declared variable")
                .clone();
            declarations.add_declaration(&name[..].into(), declaration)
        }
        declarations
    }
}

#[derive(Clone)]
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

impl Display for VariableType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use VariableType::*;
        match self {
            Var => write!(f, "var"),
            Signal(signal_type, _) => write!(f, "signal {signal_type}"),
            Component => write!(f, "component"),
        }
    }
}

impl Display for SignalType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use SignalType::*;
        match self {
            Input => write!(f, "input"),
            Output => write!(f, "output"),
            Intermediate => Ok(()), // Intermediate signals have no explicit signal type.
        }
    }
}
