use program_structure::ast::*;
use program_structure::report::ReportCollection;

use crate::errors::TupleError;

pub(crate) trait ContainsExpression {
    /// Returns true if `self` contains `expr` such that `matcher(expr)`
    /// evaluates to true. If the callback is not `None` it is invoked on
    /// `expr.meta()` for each matching expression.
    fn contains_expr(
        &self,
        matcher: &impl Fn(&Expression) -> bool,
        callback: &mut impl FnMut(&Meta),
    ) -> bool;

    /// Returns true if the node contains a tuple. If `reports` is not `None`, a
    /// report is generated for each occurrence.
    fn contains_tuple(&self, reports: Option<&mut ReportCollection>) -> bool {
        let matcher = |expr: &Expression| expr.is_tuple();
        if let Some(reports) = reports {
            let mut callback = |meta: &Meta| {
                let error = TupleError::new(
                    Some(meta),
                    "Tuples are not allowed in functions.",
                    Some("Tuple instantiated here."),
                );
                reports.push(error.into_report());
            };
            self.contains_expr(&matcher, &mut callback)
        } else {
            // We need to pass a dummy callback because rustc isn't smart enough
            // to infer the type parameter to `Option` if we use options here.
            let mut dummy = |_: &Meta| {};
            self.contains_expr(&matcher, &mut dummy)
        }
    }

    /// Returns true if the node contains an anonymous component. If `reports`
    /// is not `None`, a report is generated for each occurrence.
    fn contains_anonymous_component(&self, reports: Option<&mut ReportCollection>) -> bool {
        let matcher = |expr: &Expression| expr.is_anonymous_component();
        if let Some(reports) = reports {
            let mut callback = |meta: &Meta| {
                let error = TupleError::new(
                    Some(meta),
                    "Anonymous components are not allowed in functions.",
                    Some("Anonymous component instantiated here."),
                );
                reports.push(error.into_report());
            };
            self.contains_expr(&matcher, &mut callback)
        } else {
            // We need to pass a dummy callback because rustc isn't smart enough
            // to infer the type parameter to `Option` if we use options here.
            let mut dummy = |_: &Meta| {};
            self.contains_expr(&matcher, &mut dummy)
        }
    }
}

impl ContainsExpression for Expression {
    fn contains_expr(
        &self,
        matcher: &impl Fn(&Expression) -> bool,
        callback: &mut impl FnMut(&Meta),
    ) -> bool {
        use Expression::*;
        // Check if the current expression matches and invoke the callback if
        // defined.
        if matcher(self) {
            callback(self.meta());
            return true;
        }
        let mut result = false;
        match &self {
            InfixOp { lhe, rhe, .. } => {
                result = lhe.contains_expr(matcher, callback) || result;
                result = rhe.contains_expr(matcher, callback) || result;
                result
            }
            PrefixOp { rhe, .. } => rhe.contains_expr(matcher, callback),
            InlineSwitchOp { cond, if_true, if_false, .. } => {
                result = cond.contains_expr(matcher, callback) || result;
                result = if_true.contains_expr(matcher, callback) || result;
                result = if_false.contains_expr(matcher, callback) || result;
                result
            }
            Call { args, .. } => {
                for arg in args {
                    result = arg.contains_expr(matcher, callback) || result;
                }
                result
            }
            ArrayInLine { values, .. } => {
                for value in values {
                    result = value.contains_expr(matcher, callback) || result;
                }
                result
            }
            AnonymousComponent { params, signals, .. } => {
                for param in params {
                    result = param.contains_expr(matcher, callback) || result;
                }
                for signal in signals {
                    result = signal.contains_expr(matcher, callback) || result;
                }
                result
            }
            Variable { access, .. } => {
                for access in access {
                    if let Access::ArrayAccess(index) = access {
                        result = index.contains_expr(matcher, callback) || result;
                    }
                }
                result
            }
            Number(_, _) => false,
            Tuple { values, .. } => {
                for value in values {
                    result = value.contains_expr(matcher, callback) || result;
                }
                result
            }
            ParallelOp { rhe, .. } => rhe.contains_expr(matcher, callback),
        }
    }
}

impl ContainsExpression for Statement {
    fn contains_expr(
        &self,
        matcher: &impl Fn(&Expression) -> bool,
        callback: &mut impl FnMut(&Meta),
    ) -> bool {
        use LogArgument::*;
        use Statement::*;
        use Access::*;
        let mut result = false;
        match self {
            IfThenElse { cond, if_case, else_case, .. } => {
                result = cond.contains_expr(matcher, callback) || result;
                result = if_case.contains_expr(matcher, callback) || result;
                if let Some(else_case) = else_case {
                    result = else_case.contains_expr(matcher, callback) || result;
                }
                result
            }
            While { cond, stmt, .. } => {
                result = cond.contains_expr(matcher, callback) || result;
                result = stmt.contains_expr(matcher, callback) || result;
                result
            }
            Return { value, .. } => value.contains_expr(matcher, callback),
            InitializationBlock { initializations, .. } => {
                for init in initializations {
                    result = init.contains_expr(matcher, callback) || result;
                }
                result
            }
            Block { stmts, .. } => {
                for stmt in stmts {
                    result = stmt.contains_expr(matcher, callback) || result;
                }
                result
            }
            Declaration { dimensions, .. } => {
                for size in dimensions {
                    result = size.contains_expr(matcher, callback) || result;
                }
                result
            }
            Substitution { access, rhe, .. } => {
                for access in access {
                    if let ArrayAccess(index) = access {
                        result = index.contains_expr(matcher, callback) || result;
                    }
                }
                result = rhe.contains_expr(matcher, callback) || result;
                result
            }
            MultiSubstitution { lhe, rhe, .. } => {
                result = lhe.contains_expr(matcher, callback) || result;
                result = rhe.contains_expr(matcher, callback) || result;
                result
            }
            ConstraintEquality { lhe, rhe, .. } => {
                result = lhe.contains_expr(matcher, callback) || result;
                result = rhe.contains_expr(matcher, callback) || result;
                result
            }
            LogCall { args, .. } => {
                for arg in args {
                    if let LogExp(expr) = arg {
                        result = expr.contains_expr(matcher, callback) || result;
                    }
                }
                result
            }
            Assert { arg, .. } => arg.contains_expr(matcher, callback),
        }
    }
}
