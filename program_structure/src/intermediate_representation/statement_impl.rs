use log::trace;
use std::fmt;

use super::declarations::Declarations;
use super::ir::*;
use super::degree_meta::{Degree, DegreeEnvironment, DegreeMeta};
use super::type_meta::TypeMeta;
use super::value_meta::{ValueEnvironment, ValueMeta};
use super::variable_meta::{VariableMeta, VariableUse, VariableUses};

impl Statement {
    #[must_use]
    pub fn meta(&self) -> &Meta {
        use Statement::*;
        match self {
            Declaration { meta, .. }
            | IfThenElse { meta, .. }
            | Return { meta, .. }
            | Substitution { meta, .. }
            | LogCall { meta, .. }
            | Assert { meta, .. }
            | ConstraintEquality { meta, .. } => meta,
        }
    }

    #[must_use]
    pub fn meta_mut(&mut self) -> &mut Meta {
        use Statement::*;
        match self {
            Declaration { meta, .. }
            | IfThenElse { meta, .. }
            | Return { meta, .. }
            | Substitution { meta, .. }
            | LogCall { meta, .. }
            | Assert { meta, .. }
            | ConstraintEquality { meta, .. } => meta,
        }
    }

    pub fn propagate_degrees(&mut self, env: &mut DegreeEnvironment) -> bool {
        let mut result = false;

        use Degree::*;
        use Statement::*;
        use VariableType::*;
        match self {
            Declaration { names, var_type, .. } => {
                for name in names.iter() {
                    // Since we disregard accesses, components are treated as signals.
                    if matches!(var_type, Signal(_) | Component) {
                        result = result || env.set_degree(name, &Linear.into());
                    }
                    env.set_type(name, var_type);
                }
                result
            }
            Substitution { var, rhe, .. } => {
                result = result || rhe.propagate_degrees(env);
                if env.is_local(var) {
                    if let Some(range) = rhe.degree() {
                        result = result || env.set_degree(var, range);
                    }
                }
                result
            }
            LogCall { args, .. } => {
                use LogArgument::*;
                for arg in args {
                    if let Expr(value) = arg {
                        result = result || value.propagate_degrees(env);
                    }
                }
                result
            }
            IfThenElse { cond, .. } => cond.propagate_degrees(env),
            Return { value, .. } => value.propagate_degrees(env),
            Assert { arg, .. } => arg.propagate_degrees(env),
            ConstraintEquality { lhe, rhe, .. } => {
                result = result || lhe.propagate_degrees(env);
                result = result || rhe.propagate_degrees(env);
                result
            }
        }
    }

    #[must_use]
    pub fn propagate_values(&mut self, env: &mut ValueEnvironment) -> bool {
        use Statement::*;
        use Expression::*;
        match self {
            Declaration { dimensions, .. } => {
                let mut result = false;
                for size in dimensions {
                    result = result || size.propagate_values(env);
                }
                result
            }
            Substitution { meta, var, rhe, .. } => {
                let mut result = rhe.propagate_values(env);

                // TODO: Handle array values.
                if !matches!(rhe, Update { .. }) {
                    if let Some(value) = rhe.value() {
                        env.add_variable(var, value);
                        result = result || meta.value_knowledge_mut().set_reduces_to(value.clone());
                    }
                }
                trace!("Substitution returned {result}");
                result
            }
            LogCall { args, .. } => {
                let mut result = false;
                use LogArgument::*;
                for arg in args {
                    if let Expr(value) = arg {
                        result = result || value.propagate_values(env);
                    }
                }
                result
            }
            IfThenElse { cond, .. } => cond.propagate_values(env),
            Return { value, .. } => value.propagate_values(env),
            Assert { arg, .. } => arg.propagate_values(env),
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.propagate_values(env) || rhe.propagate_values(env)
            }
        }
    }

    pub fn propagate_types(&mut self, vars: &Declarations) {
        use Statement::*;
        match self {
            Declaration { meta, var_type, dimensions, .. } => {
                // The metadata tracks the type of the declared variable.
                meta.type_knowledge_mut().set_variable_type(var_type);
                for size in dimensions {
                    size.propagate_types(vars);
                }
            }
            Substitution { meta, var, rhe, .. } => {
                // The metadata tracks the type of the assigned variable.
                rhe.propagate_types(vars);
                if let Some(var_type) = vars.get_type(var) {
                    meta.type_knowledge_mut().set_variable_type(var_type);
                }
            }
            LogCall { args, .. } => {
                use LogArgument::*;
                for arg in args {
                    if let Expr(value) = arg {
                        value.propagate_types(vars);
                    }
                }
            }
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.propagate_types(vars);
                rhe.propagate_types(vars);
            }
            IfThenElse { cond, .. } => {
                cond.propagate_types(vars);
            }
            Return { value, .. } => {
                value.propagate_types(vars);
            }
            Assert { arg, .. } => {
                arg.propagate_types(vars);
            }
        }
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Statement::*;
        match self {
            Declaration { names, var_type, dimensions, .. } => {
                write!(f, "{var_type} ")?;
                let mut first = true;
                for name in names {
                    if first {
                        first = false;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name:?}")?;
                    for size in dimensions {
                        write!(f, "[{size:?}]")?;
                    }
                }
                Ok(())
            }
            Substitution { var, op, rhe, .. } => write!(f, "{var:?} {op} {rhe:?}"),
            ConstraintEquality { lhe, rhe, .. } => write!(f, "{lhe:?} === {rhe:?}"),
            IfThenElse { cond, true_index, false_index, .. } => match false_index {
                Some(false_index) => write!(f, "if {cond:?} then {true_index} else {false_index}"),
                None => write!(f, "if {cond:?} then {true_index}"),
            },
            Return { value, .. } => write!(f, "return {value:?}"),
            Assert { arg, .. } => write!(f, "assert({arg:?})"),
            LogCall { args, .. } => write!(f, "log({:?})", vec_to_debug(args, ", ")),
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Statement::*;
        match self {
            Declaration { names, var_type, dimensions, .. } => {
                // We rewrite declarations of multiple SSA variables as a single
                // declaration of the original variable.
                write!(f, "{var_type} {}", names.first())?;
                for size in dimensions {
                    write!(f, "[{size}]")?;
                }
                Ok(())
            }
            Substitution { var, op, rhe, .. } => {
                match rhe {
                    // We rewrite `Update` expressions of arrays/component signals.
                    Expression::Update { access, rhe, .. } => {
                        write!(f, "{var}")?;
                        for access in access {
                            write!(f, "{access}")?;
                        }
                        write!(f, " {op} {rhe}")
                    }
                    // This is an ordinary assignment.
                    _ => write!(f, "{var} {op} {rhe}"),
                }
            }
            ConstraintEquality { lhe, rhe, .. } => write!(f, "{lhe} === {rhe}"),
            IfThenElse { cond, .. } => write!(f, "if {cond}"),
            Return { value, .. } => write!(f, "return {value}"),
            Assert { arg, .. } => write!(f, "assert({arg})"),
            LogCall { args, .. } => write!(f, "log({})", vec_to_display(args, ", ")),
        }
    }
}

impl fmt::Display for AssignOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use AssignOp::*;
        match self {
            AssignSignal => write!(f, "<--"),
            AssignConstraintSignal => write!(f, "<=="),
            AssignLocalOrComponent => write!(f, "="),
        }
    }
}

impl fmt::Display for LogArgument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use LogArgument::*;
        match self {
            String(message) => write!(f, "{message}"),
            Expr(value) => write!(f, "{value}"),
        }
    }
}

impl fmt::Debug for LogArgument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use LogArgument::*;
        match self {
            String(message) => write!(f, "{message:?}"),
            Expr(value) => write!(f, "{value:?}"),
        }
    }
}

impl VariableMeta for Statement {
    fn cache_variable_use(&mut self) {
        let mut locals_read = VariableUses::new();
        let mut locals_written = VariableUses::new();
        let mut signals_read = VariableUses::new();
        let mut signals_written = VariableUses::new();
        let mut components_read = VariableUses::new();
        let mut components_written = VariableUses::new();

        use Statement::*;
        use Expression::*;
        match self {
            Declaration { dimensions, .. } => {
                for size in dimensions {
                    size.cache_variable_use();
                    locals_read.extend(size.locals_read().clone());
                    signals_read.extend(size.signals_read().clone());
                    components_read.extend(size.components_read().clone());
                }
            }
            Substitution { meta, var, op, rhe } => {
                rhe.cache_variable_use();
                locals_read.extend(rhe.locals_read().clone());
                signals_read.extend(rhe.signals_read().clone());
                components_read.extend(rhe.components_read().clone());

                let access = match rhe {
                    Update { access, .. } => access.clone(),
                    _ => Vec::new(),
                };
                match meta.type_knowledge().variable_type() {
                    Some(VariableType::Local) => {
                        trace!("adding `{var:?}` to local variables written");
                        locals_written.insert(VariableUse::new(meta, var, &access));
                    }
                    Some(VariableType::Signal(_)) => {
                        trace!("adding `{var:?}` to signals written");
                        signals_written.insert(VariableUse::new(meta, var, &access));
                        if matches!(op, AssignOp::AssignConstraintSignal) {
                            // If this is a signal constraint assignment, we
                            // consider the assigned signal to be read as well.
                            trace!("adding `{var:?}` to signals read");
                            signals_read.insert(VariableUse::new(meta, var, &access));
                        }
                    }
                    Some(VariableType::Component) => {
                        trace!("adding `{var:?}` to components written");
                        components_written.insert(VariableUse::new(meta, var, &access));
                    }
                    None => {
                        trace!("variable `{var:?}` of unknown type written");
                    }
                }
            }
            LogCall { args, .. } => {
                use LogArgument::*;
                for arg in args {
                    if let Expr(value) = arg {
                        value.cache_variable_use();
                        locals_read.extend(value.locals_read().clone());
                        signals_read.extend(value.signals_read().clone());
                        components_read.extend(value.components_read().clone());
                    }
                }
            }
            IfThenElse { cond, .. } => {
                cond.cache_variable_use();
                locals_read.extend(cond.locals_read().clone());
                signals_read.extend(cond.signals_read().clone());
                components_read.extend(cond.components_read().clone());
            }
            Return { value, .. } => {
                value.cache_variable_use();
                locals_read.extend(value.locals_read().clone());
                signals_read.extend(value.signals_read().clone());
                components_read.extend(value.components_read().clone());
            }
            Assert { arg, .. } => {
                arg.cache_variable_use();
                locals_read.extend(arg.locals_read().clone());
                signals_read.extend(arg.signals_read().clone());
                components_read.extend(arg.components_read().clone());
            }
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                locals_read.extend(lhe.locals_read().iter().cloned());
                locals_read.extend(rhe.locals_read().iter().cloned());
                signals_read.extend(lhe.signals_read().iter().cloned());
                signals_read.extend(rhe.signals_read().iter().cloned());
                components_read.extend(lhe.components_read().iter().cloned());
                components_read.extend(rhe.components_read().iter().cloned());
            }
        }
        self.meta_mut()
            .variable_knowledge_mut()
            .set_locals_read(&locals_read)
            .set_locals_written(&locals_written)
            .set_signals_read(&signals_read)
            .set_signals_written(&signals_written)
            .set_components_read(&components_read)
            .set_components_written(&components_written);
    }

    fn locals_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().locals_read()
    }

    fn locals_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().locals_written()
    }

    fn signals_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().signals_read()
    }

    fn signals_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().signals_written()
    }

    fn components_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().components_read()
    }

    fn components_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().components_written()
    }
}

#[must_use]
fn vec_to_debug<T: fmt::Debug>(elems: &[T], sep: &str) -> String {
    elems.iter().map(|elem| format!("{elem:?}")).collect::<Vec<String>>().join(sep)
}

#[must_use]
fn vec_to_display<T: fmt::Display>(elems: &[T], sep: &str) -> String {
    elems.iter().map(|elem| format!("{elem}")).collect::<Vec<String>>().join(sep)
}
