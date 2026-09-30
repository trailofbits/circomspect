use program_structure::ast::*;
use program_structure::report::ReportCollection;

use crate::errors::TupleError;

/// Visits every expression in an AST node, including nested call arguments.
pub(crate) trait ContainsExpression {
    fn visit_expressions(&self, visitor: &mut impl FnMut(&Expression));

    fn contains_expr(
        &self,
        matcher: &impl Fn(&Expression) -> bool,
        callback: &mut impl FnMut(&Meta),
    ) -> bool {
        let mut found = false;
        self.visit_expressions(&mut |expression| {
            if matcher(expression) {
                found = true;
                callback(expression.meta());
            }
        });
        found
    }

    fn contains_tuple(&self, reports: Option<&mut ReportCollection>) -> bool {
        let matcher = |expression: &Expression| expression.is_tuple();
        if let Some(reports) = reports {
            let mut callback = |meta: &Meta| {
                reports.push(
                    TupleError::new(
                        Some(meta),
                        "Tuples are not allowed in functions.",
                        Some("Tuple instantiated here."),
                    )
                    .into_report(),
                );
            };
            self.contains_expr(&matcher, &mut callback)
        } else {
            self.contains_expr(&matcher, &mut |_: &Meta| {})
        }
    }

    fn contains_anonymous_component(&self, reports: Option<&mut ReportCollection>) -> bool {
        let matcher = |expression: &Expression| expression.is_anonymous_component();
        if let Some(reports) = reports {
            let mut callback = |meta: &Meta| {
                reports.push(
                    TupleError::new(
                        Some(meta),
                        "Anonymous components are not allowed in functions.",
                        Some("Anonymous component instantiated here."),
                    )
                    .into_report(),
                );
            };
            self.contains_expr(&matcher, &mut callback)
        } else {
            self.contains_expr(&matcher, &mut |_: &Meta| {})
        }
    }
}

impl ContainsExpression for Expression {
    fn visit_expressions(&self, visitor: &mut impl FnMut(&Expression)) {
        use Expression::*;

        visitor(self);
        match self {
            InfixOp { lhe, rhe, .. } => {
                lhe.visit_expressions(visitor);
                rhe.visit_expressions(visitor);
            }
            PrefixOp { rhe, .. } | ParallelOp { rhe, .. } => rhe.visit_expressions(visitor),
            InlineSwitchOp { cond, if_true, if_false, .. } => {
                cond.visit_expressions(visitor);
                if_true.visit_expressions(visitor);
                if_false.visit_expressions(visitor);
            }
            Variable { access, .. } => {
                for access in access {
                    if let Access::ArrayAccess(index) = access {
                        index.visit_expressions(visitor);
                    }
                }
            }
            Number(_, _) => {}
            Call { args, .. } => {
                for arg in args {
                    arg.visit_expressions(visitor);
                }
            }
            AnonymousComponent { params, signals, .. } => {
                for param in params {
                    param.visit_expressions(visitor);
                }
                for signal in signals {
                    signal.visit_expressions(visitor);
                }
            }
            ArrayInLine { values, .. } | Tuple { values, .. } => {
                for value in values {
                    value.visit_expressions(visitor);
                }
            }
        }
    }
}

impl ContainsExpression for Statement {
    fn visit_expressions(&self, visitor: &mut impl FnMut(&Expression)) {
        use Access::*;
        use LogArgument::*;
        use Statement::*;

        match self {
            IfThenElse { cond, if_case, else_case, .. } => {
                cond.visit_expressions(visitor);
                if_case.visit_expressions(visitor);
                if let Some(else_case) = else_case {
                    else_case.visit_expressions(visitor);
                }
            }
            While { cond, stmt, .. } => {
                cond.visit_expressions(visitor);
                stmt.visit_expressions(visitor);
            }
            Return { value, .. } => value.visit_expressions(visitor),
            InitializationBlock { initializations, .. } => {
                for initialization in initializations {
                    initialization.visit_expressions(visitor);
                }
            }
            Declaration { dimensions, .. } => {
                for dimension in dimensions {
                    dimension.visit_expressions(visitor);
                }
            }
            Substitution { access, rhe, .. } => {
                for access in access {
                    if let ArrayAccess(index) = access {
                        index.visit_expressions(visitor);
                    }
                }
                rhe.visit_expressions(visitor);
            }
            MultiSubstitution { lhe, rhe, .. } | ConstraintEquality { lhe, rhe, .. } => {
                lhe.visit_expressions(visitor);
                rhe.visit_expressions(visitor);
            }
            LogCall { args, .. } => {
                for argument in args {
                    if let LogExp(expression) = argument {
                        expression.visit_expressions(visitor);
                    }
                }
            }
            Block { stmts, .. } => {
                for statement in stmts {
                    statement.visit_expressions(visitor);
                }
            }
            Assert { arg, .. } => arg.visit_expressions(visitor),
        }
    }
}
