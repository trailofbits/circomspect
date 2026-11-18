//! Source-level range obligations for direct LessThan(n) calls.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::ToPrimitive;
use parser::frontend::{AssignmentOperator, BinaryOperator, InputAssignmentOperator, PostfixOperator};
use parser::hir::{
    BlockId, CallTarget, DefinitionRef, Effect, ExprId, ExprKind, FunctionId, Knownness, SymbolId,
};

use crate::hir_facts::{FieldContext, FieldValue, Range};
use crate::interprocedural::ArgumentValue;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub(super) struct ComparatorPrecondition;

struct RangeEnvironment {
    field: FieldContext,
    parameters: BTreeMap<SymbolId, FieldValue>,
    bits: u32,
    bound: BigInt,
}

enum EvaluationFlow {
    Continue,
    Return(FieldValue),
}

struct EvaluationBudget {
    depth: usize,
    steps: usize,
}

impl Rule for ComparatorPrecondition {
    fn kind(&self) -> RuleKind {
        RuleKind::ComparatorPrecondition
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let DefinitionRef::Template(id) = context.call_context().definition() else {
            return result;
        };
        let Some(template) = context.hir().template(id) else { return result };
        let Some(body) = context.hir().block(template.body) else { return result };
        let Some(parameters) = concrete_parameters(context, &template.parameters) else {
            return result;
        };
        if let Err(blocker) = context.validated_definition() {
            result.add_abstention(context.abstention(
                self.kind(),
                template.name_span,
                AbstentionReason::Summary(BTreeSet::from([blocker])),
            ));
        }
        let field = FieldContext::for_curve(context.facts().curve().clone());
        for expression in context.hir().expressions() {
            abstract_interpretation::timeout::check();
            if !inside_body(expression.span, body.span) {
                continue;
            }
            let ExprKind::AnonymousComponent { component, .. } = expression.kind else {
                continue;
            };
            let Some(CallTarget::Template(target)) =
                context.hir().component(component).and_then(|item| item.target.as_ref())
            else {
                continue;
            };
            if context.hir().template(*target).map_or(true, |item| item.name != "LessThan") {
                continue;
            }
            if context.facts().reachable_expression(expression.id).certified() == Some(&false) {
                continue;
            }
            inspect_call(context, expression.id, &field, &parameters, &mut result);
        }
        result
    }
}

fn inside_body(inner: parser::frontend::Span, outer: parser::frontend::Span) -> bool {
    inner.source() == outer.source() && inner.start() >= outer.start() && inner.end() <= outer.end()
}

fn concrete_parameters(
    context: &RuleContext<'_, '_, '_>,
    symbols: &[SymbolId],
) -> Option<BTreeMap<SymbolId, FieldValue>> {
    let mut values = BTreeMap::new();
    for (symbol, argument) in symbols.iter().zip(context.call_context().arguments()) {
        match argument {
            ArgumentValue::Scalar(value) => {
                values.insert(*symbol, value.clone());
            }
            ArgumentValue::Symbolic(_) => {}
            ArgumentValue::Array(_) | ArgumentValue::Bus(_) => return None,
        }
    }
    Some(values)
}

fn exact_integer(
    context: &RuleContext<'_, '_, '_>,
    id: ExprId,
    field: &FieldContext,
    parameters: &BTreeMap<SymbolId, FieldValue>,
) -> Option<BigInt> {
    if let Some(Range::Exact(value)) = context.facts().range(id).certified() {
        return Some(value.as_bigint().clone());
    }
    evaluate(context, id, field, parameters, 0).map(|value| value.as_bigint().clone())
}

fn evaluate(
    context: &RuleContext<'_, '_, '_>,
    id: ExprId,
    field: &FieldContext,
    parameters: &BTreeMap<SymbolId, FieldValue>,
    depth: usize,
) -> Option<FieldValue> {
    if depth > 32 {
        return None;
    }
    let expression = context.hir().expression(id)?;
    match &expression.kind {
        ExprKind::Number(text) => field.parse(text),
        ExprKind::Access(path) if path.steps.is_empty() => parameters.get(&path.root).cloned(),
        ExprKind::Binary { operator, left, right } => {
            let left = evaluate(context, *left, field, parameters, depth + 1)?;
            let right = evaluate(context, *right, field, parameters, depth + 1)?;
            match operator {
                BinaryOperator::Add => Some(field.add(&left, &right)),
                BinaryOperator::Subtract => Some(field.subtract(&left, &right)),
                BinaryOperator::Multiply => Some(field.multiply(&left, &right)),
                BinaryOperator::Greater => Some(field.canonical(
                    i32::from(field.compare_signed(&left, &right) == Ordering::Greater).into(),
                )),
                _ => None,
            }
        }
        ExprKind::Call { target: CallTarget::Function(function), arguments } => {
            let arguments = arguments
                .iter()
                .map(|argument| evaluate(context, *argument, field, parameters, depth + 1))
                .collect::<Option<Vec<_>>>()?;
            context
                .exact_function_result(*function, arguments.clone())
                .or_else(|| evaluate_function(context, *function, field, arguments, depth + 1))
        }
        _ => None,
    }
}

fn evaluate_function(
    context: &RuleContext<'_, '_, '_>,
    function: FunctionId,
    field: &FieldContext,
    arguments: Vec<FieldValue>,
    depth: usize,
) -> Option<FieldValue> {
    if depth > 8 {
        return None;
    }
    if !context.function_has_no_hard_source_issue(function) {
        return None;
    }
    let function = context.hir().function(function)?;
    if function.parameters.len() != arguments.len() {
        return None;
    }
    let mut variables = function.parameters.iter().copied().zip(arguments).collect();
    let mut budget = EvaluationBudget { depth, steps: 0 };
    match evaluate_block(context, function.body, field, &mut variables, &mut budget)? {
        EvaluationFlow::Continue => None,
        EvaluationFlow::Return(value) => Some(value),
    }
}

fn evaluate_block(
    context: &RuleContext<'_, '_, '_>,
    block: BlockId,
    field: &FieldContext,
    variables: &mut BTreeMap<SymbolId, FieldValue>,
    budget: &mut EvaluationBudget,
) -> Option<EvaluationFlow> {
    for effect in &context.hir().block(block)?.effects {
        abstract_interpretation::timeout::check();
        budget.steps += 1;
        if budget.steps > 1024 {
            return None;
        }
        match evaluate_effect(context, effect, field, variables, budget)? {
            EvaluationFlow::Continue => {}
            returned @ EvaluationFlow::Return(_) => return Some(returned),
        }
    }
    Some(EvaluationFlow::Continue)
}

fn evaluate_effect(
    context: &RuleContext<'_, '_, '_>,
    effect: &Effect,
    field: &FieldContext,
    variables: &mut BTreeMap<SymbolId, FieldValue>,
    budget: &mut EvaluationBudget,
) -> Option<EvaluationFlow> {
    match effect {
        Effect::Declaration { .. } => Some(EvaluationFlow::Continue),
        Effect::VariableAssignment { target, value, operator, .. }
        | Effect::DeferredVariableAssignment { target, value, operator, .. } => {
            if !target.steps.is_empty() {
                return None;
            }
            let value = evaluate(context, *value, field, variables, budget.depth + 1)?;
            let value = assigned_value(field, variables.get(&target.root), &value, *operator)?;
            variables.insert(target.root, value);
            Some(EvaluationFlow::Continue)
        }
        Effect::Update { target, operator, .. } if target.steps.is_empty() => {
            let old = variables.get(&target.root)?;
            let one = field.canonical(1.into());
            let value = match operator {
                PostfixOperator::Increment => field.add(old, &one),
                PostfixOperator::Decrement => field.subtract(old, &one),
            };
            variables.insert(target.root, value);
            Some(EvaluationFlow::Continue)
        }
        Effect::While { condition, body, .. } => {
            evaluate_while(context, (*condition, *body), field, variables, budget)
        }
        Effect::Block(block) => evaluate_block(context, *block, field, variables, budget),
        Effect::Return { value, .. } => {
            evaluate(context, *value, field, variables, budget.depth + 1)
                .map(EvaluationFlow::Return)
        }
        _ => None,
    }
}

fn evaluate_while(
    context: &RuleContext<'_, '_, '_>,
    loop_parts: (ExprId, BlockId),
    field: &FieldContext,
    variables: &mut BTreeMap<SymbolId, FieldValue>,
    budget: &mut EvaluationBudget,
) -> Option<EvaluationFlow> {
    let (condition, body) = loop_parts;
    loop {
        abstract_interpretation::timeout::check();
        let value = evaluate(context, condition, field, variables, budget.depth + 1)?;
        if field.is_zero(&value) {
            return Some(EvaluationFlow::Continue);
        }
        budget.steps += 1;
        if budget.steps > 1024 {
            return None;
        }
        match evaluate_block(context, body, field, variables, budget)? {
            EvaluationFlow::Continue => {}
            returned @ EvaluationFlow::Return(_) => return Some(returned),
        }
    }
}

fn assigned_value(
    field: &FieldContext,
    previous: Option<&FieldValue>,
    value: &FieldValue,
    operator: AssignmentOperator,
) -> Option<FieldValue> {
    match operator {
        AssignmentOperator::Assign => Some(value.clone()),
        AssignmentOperator::IntegerDivide => {
            let previous = previous?;
            let half = field.modulus() / 2;
            if field.is_zero(value) || previous.as_bigint() > &half || value.as_bigint() > &half {
                return None;
            }
            Some(field.canonical(previous.as_bigint() / value.as_bigint()))
        }
        _ => None,
    }
}

fn inspect_call(
    context: &RuleContext<'_, '_, '_>,
    id: ExprId,
    field: &FieldContext,
    parameters: &BTreeMap<SymbolId, FieldValue>,
    result: &mut RuleResult,
) {
    let Some(expression) = context.hir().expression(id) else { return };
    let ExprKind::AnonymousComponent { arguments, inputs, .. } = &expression.kind else {
        return;
    };
    let Some(bits) = arguments
        .first()
        .and_then(|id| exact_integer(context, *id, field, parameters))
        .and_then(|value| value.to_u32())
    else {
        result.add_abstention(context.abstention(
            RuleKind::ComparatorPrecondition,
            expression.span,
            AbstentionReason::SymbolicParameters,
        ));
        return;
    };
    let Ok(width) = usize::try_from(bits) else { return };
    let bound = BigInt::from(1u8) << width;
    if bits == 0 || &bound * 2 >= *field.modulus() {
        return;
    }
    let environment =
        RangeEnvironment { field: field.clone(), parameters: parameters.clone(), bits, bound };
    for input in inputs {
        if input.operator != InputAssignmentOperator::Constraint {
            continue;
        }
        let Some(array) = context.hir().expression(input.value) else { continue };
        let ExprKind::Array(operands) = &array.kind else { continue };
        if operands.len() != 2 {
            continue;
        }
        for (position, operand) in operands.iter().enumerate() {
            inspect_operand(context, *operand, position, &environment, result);
        }
    }
}

fn inspect_operand(
    context: &RuleContext<'_, '_, '_>,
    operand: ExprId,
    position: usize,
    environment: &RangeEnvironment,
    result: &mut RuleResult,
) {
    let Some(expression) = context.hir().expression(operand) else { return };
    if let Some(value) =
        exact_integer(context, operand, &environment.field, &environment.parameters)
    {
        if value >= environment.bound {
            result.add_finding(context.finding(
                RuleKind::ComparatorPrecondition,
                format!(
                    "LessThan({}) input {position} is {value}, outside the standard integer \
                     range [0, {}).",
                    environment.bits, environment.bound
                ),
                expression.span,
                "This comparator operand is outside its required range.".into(),
            ));
        }
        return;
    }
    if expression.knownness != Knownness::WitnessDependent {
        return;
    }
    let subject = match &expression.kind {
        ExprKind::Access(path) if path.steps.is_empty() => context
            .hir()
            .symbol(path.root)
            .map_or_else(|| "this input".to_owned(), |symbol| format!("`{}`", symbol.name)),
        _ => "this input".to_owned(),
    };
    result.add_finding(context.finding(
        RuleKind::ComparatorPrecondition,
        format!("Failed to prove that {subject} is constrained to be {} bits.", environment.bits),
        expression.span,
        "This input to `LessThan` may not be properly constrained.".into(),
    ));
}
