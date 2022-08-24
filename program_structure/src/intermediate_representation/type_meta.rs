use super::declarations::Declarations;
use super::ir::VariableType;

pub trait TypeMeta {
    /// Propagate variable types to variable child nodes.
    fn propagate_types(&mut self, vars: &Declarations);

    /// Returns true if the node is a local variable.
    #[must_use]
    fn is_local(&self) -> bool;

    /// Returns true if the node is a signal.
    #[must_use]
    fn is_signal(&self) -> bool;

    /// Returns true if the node is a component.
    #[must_use]
    fn is_component(&self) -> bool;

    /// For declared variables, this returns the type. For undeclared variables
    /// and other expression nodes this returns `None`.
    #[must_use]
    fn variable_type(&self) -> Option<&VariableType>;
}

#[derive(Default, Clone)]
pub struct TypeKnowledge {
    var_type: Option<VariableType>,
}

impl TypeKnowledge {
    #[must_use]
    pub fn new() -> TypeKnowledge {
        TypeKnowledge::default()
    }

    pub fn set_variable_type(&mut self, var_type: &VariableType) {
        self.var_type = Some(var_type.clone());
    }

    #[must_use]
    pub fn variable_type(&self) -> Option<&VariableType> {
        self.var_type.as_ref()
    }

    /// Returns true if the node is a local variable.
    #[must_use]
    pub fn is_local(&self) -> bool {
        matches!(self.var_type, Some(VariableType::Local { .. }))
    }

    /// Returns true if the node is a signal.
    #[must_use]
    pub fn is_signal(&self) -> bool {
        matches!(self.var_type, Some(VariableType::Signal { .. }))
    }

    /// Returns true if the node is a component.
    #[must_use]
    pub fn is_component(&self) -> bool {
        matches!(self.var_type, Some(VariableType::Component { .. }))
    }
}
