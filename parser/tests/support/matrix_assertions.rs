use circomspect_parser::frontend::{
    Access, AnonymousCallExpr, AnonymousInput, ArgumentList, AssignmentOperator, BinaryOperator,
    Declaration, DeclarationKind, Definition, DefinitionKind, DirectionSyntax, Expression,
    InputAssignmentOperator, Item, LogArgument, PortDirection, PostfixOperator, Pragma, SourceAst,
    Span, Statement, SymbolSyntax, Trivia, TriviaKind, UnaryOperator,
};
use serde_json::Value;
use std::ops::Range;

#[derive(Clone, Copy)]
enum Node<'a> {
    Item(&'a Item),
    Definition(&'a Definition),
    Statement(&'a Statement),
    Declaration(&'a Declaration),
    Expression(&'a Expression),
    Trivia(&'a Trivia),
}

impl Node<'_> {
    fn span(self) -> Span {
        match self {
            Self::Item(value) => value.span(),
            Self::Definition(value) => value.span,
            Self::Statement(value) => value.span(),
            Self::Declaration(value) => value.span,
            Self::Expression(value) => value.span(),
            Self::Trivia(value) => value.span,
        }
    }

    fn kind(self) -> &'static str {
        match self {
            Self::Item(Item::Pragma { .. }) => "pragma",
            Self::Item(Item::Include { .. }) => "include",
            Self::Item(Item::Main { .. }) => "main",
            Self::Item(Item::Definition(_) | Item::Error { .. }) => "other_item",
            Self::Definition(Definition { kind: DefinitionKind::Function, .. }) => {
                "function_definition"
            }
            Self::Definition(Definition { kind: DefinitionKind::Template { .. }, .. }) => {
                "template_definition"
            }
            Self::Definition(Definition { kind: DefinitionKind::Bus, .. }) => "bus_definition",
            Self::Declaration(Declaration { kind: DeclarationKind::Variable, .. }) => {
                "variable_declaration"
            }
            Self::Declaration(Declaration { kind: DeclarationKind::Component, .. }) => {
                "component_declaration"
            }
            Self::Declaration(Declaration { kind: DeclarationKind::Signal { .. }, .. }) => {
                "signal_declaration"
            }
            Self::Declaration(Declaration { kind: DeclarationKind::Bus { .. }, .. }) => {
                "bus_declaration"
            }
            Self::Statement(Statement::Block(_)) => "block",
            Self::Statement(Statement::Assignment { .. }) => "assignment",
            Self::Statement(Statement::PostfixUpdate { .. }) => "postfix_update",
            Self::Statement(Statement::Constraint { .. }) => "constraint",
            Self::Statement(Statement::If { .. }) => "if",
            Self::Statement(Statement::For { .. }) => "for",
            Self::Statement(Statement::While { .. }) => "while",
            Self::Statement(Statement::Return { .. }) => "return",
            Self::Statement(Statement::Assert { .. }) => "assert",
            Self::Statement(Statement::Log { .. }) => "log",
            Self::Statement(Statement::AnonymousCall { .. }) => "anonymous_call_statement",
            Self::Statement(Statement::Declaration(_) | Statement::Error { .. }) => "other_stmt",
            Self::Expression(Expression::Name { .. }) => "name",
            Self::Expression(Expression::Number { .. }) => "number",
            Self::Expression(Expression::Call { .. }) => "call",
            Self::Expression(Expression::AnonymousCall(_)) => "anonymous_call",
            Self::Expression(Expression::Array { .. }) => "array",
            Self::Expression(Expression::Tuple { .. }) => "tuple",
            Self::Expression(Expression::Unary { .. }) => "unary",
            Self::Expression(Expression::Binary { .. }) => "binary",
            Self::Expression(Expression::Ternary { .. }) => "ternary",
            Self::Expression(Expression::Parallel { .. }) => "parallel",
            Self::Expression(Expression::Group { .. }) => "group",
            Self::Expression(Expression::Error { .. }) => "error_expr",
            Self::Trivia(_) => "trivia",
        }
    }
}

pub fn assert_expectation(
    ast: &SourceAst,
    expected: &Value,
    focal: Range<usize>,
) -> Result<(), String> {
    let kind = expected["kind"].as_str().ok_or("missing AST expectation kind")?;
    if kind == "source_ast" {
        return check_source_ast(ast, expected);
    }
    if kind == "item_order" {
        return check_item_order(ast, expected);
    }
    let mut nodes = Vec::new();
    for trivia in &ast.trivia {
        nodes.push(Node::Trivia(trivia));
    }
    for item in &ast.items {
        collect_item(item, &mut nodes);
    }
    if kind == "trivia" {
        if nodes.iter().any(|node| {
            node.kind() != "trivia"
                && node.span().start() <= focal.start
                && node.span().end() >= focal.end
        }) {
            return Err("comment span was converted to a syntax node".into());
        }
        nodes.retain(|node| {
            node.kind() == "trivia"
                && node.span().start() == focal.start
                && node.span().end() == focal.end
        });
    } else {
        nodes.retain(|node| {
            let span = node.span();
            span.start() <= focal.start && span.end() >= focal.end && node.kind() == kind
        });
    }
    nodes.sort_by_key(|node| node.span().end() - node.span().start());
    let mut errors = Vec::new();
    for node in nodes {
        match check_node(node, expected) {
            Ok(()) => return Ok(()),
            Err(error) => errors.push(error),
        }
    }
    if errors.is_empty() {
        Err(format!("no typed {kind} node covers {}..{}", focal.start, focal.end))
    } else {
        Err(format!("typed {kind} mismatch: {}", errors.join("; ")))
    }
}

fn check_source_ast(ast: &SourceAst, expected: &Value) -> Result<(), String> {
    for fact in expected["modifier"].as_str().unwrap_or("").split(';') {
        let (key, value) = fact.split_once('=').ok_or("invalid source AST fact")?;
        match key {
            "main" if value == "absent" => {
                for item in &ast.items {
                    if let Item::Main { .. } = item {
                        return Err("library unexpectedly has a main component".into());
                    }
                }
            }
            "definitions" => {
                let count = ast
                    .items
                    .iter()
                    .filter_map(|item| {
                        let Item::Definition(definition) = item else {
                            return None;
                        };
                        Some(definition)
                    })
                    .count();
                check_equal("definition count", count.to_string(), value)?;
            }
            _ => return Err(format!("unknown source AST fact {fact}")),
        }
    }
    Ok(())
}

fn check_item_order(ast: &SourceAst, expected: &Value) -> Result<(), String> {
    let actual: Vec<_> = ast
        .items
        .iter()
        .map(|item| match item {
            Item::Pragma { .. } => "pragma",
            Item::Include { .. } => "include",
            Item::Main { .. } => "main",
            Item::Definition(Definition { kind: DefinitionKind::Function, .. }) => "function",
            Item::Definition(Definition { kind: DefinitionKind::Template { .. }, .. }) => {
                "template"
            }
            Item::Definition(Definition { kind: DefinitionKind::Bus, .. }) => "bus",
            Item::Error { .. } => "error",
        })
        .collect();
    check_equal("item order", actual.join(","), expected["shape"].as_str().unwrap_or(""))
}

fn check_equal(label: &str, actual: impl AsRef<str>, expected: &str) -> Result<(), String> {
    if actual.as_ref() == expected {
        Ok(())
    } else {
        Err(format!("{label}: expected {expected}, found {}", actual.as_ref()))
    }
}

fn collect_item<'a>(item: &'a Item, nodes: &mut Vec<Node<'a>>) {
    nodes.push(Node::Item(item));
    match item {
        Item::Definition(definition) => {
            nodes.push(Node::Definition(definition));
            for statement in &definition.body.statements {
                collect_statement(statement, nodes);
            }
        }
        Item::Main { instance, .. } => collect_expression(instance, nodes),
        Item::Pragma { .. } | Item::Include { .. } | Item::Error { .. } => {}
    }
}

fn collect_statement<'a>(statement: &'a Statement, nodes: &mut Vec<Node<'a>>) {
    nodes.push(Node::Statement(statement));
    match statement {
        Statement::Block(block) => {
            for statement in &block.statements {
                collect_statement(statement, nodes);
            }
        }
        Statement::Declaration(declaration) => collect_declaration(declaration, nodes),
        Statement::Assignment { target, value, .. }
        | Statement::Constraint { left: target, right: value, .. } => {
            collect_expression(target, nodes);
            collect_expression(value, nodes);
        }
        Statement::PostfixUpdate { target, .. }
        | Statement::Return { value: target, .. }
        | Statement::Assert { condition: target, .. } => collect_expression(target, nodes),
        Statement::If { condition, then_branch, else_branch, .. } => {
            collect_expression(condition, nodes);
            collect_statement(then_branch, nodes);
            if let Some(else_branch) = else_branch {
                collect_statement(else_branch, nodes);
            }
        }
        Statement::For { initializer, condition, step, body, .. } => {
            collect_statement(initializer, nodes);
            collect_expression(condition, nodes);
            collect_statement(step, nodes);
            collect_statement(body, nodes);
        }
        Statement::While { condition, body, .. } => {
            collect_expression(condition, nodes);
            collect_statement(body, nodes);
        }
        Statement::Log { arguments, .. } => {
            for argument in arguments {
                if let LogArgument::Expression(expression) = argument {
                    collect_expression(expression, nodes);
                }
            }
        }
        Statement::AnonymousCall { call, .. } => collect_anonymous(call, nodes),
        Statement::Error { .. } => {}
    }
}

fn collect_declaration<'a>(declaration: &'a Declaration, nodes: &mut Vec<Node<'a>>) {
    nodes.push(Node::Declaration(declaration));
    if let DeclarationKind::Bus { arguments, .. } = &declaration.kind {
        for argument in arguments.values() {
            collect_expression(argument, nodes);
        }
    }
    for symbol in &declaration.symbols {
        for dimension in &symbol.dimensions {
            collect_expression(dimension, nodes);
        }
        if let Some((_, expression)) = &symbol.initialization {
            collect_expression(expression, nodes);
        }
    }
    if let Some((_, expression)) = &declaration.tuple_initialization {
        collect_expression(expression, nodes);
    }
}

fn collect_anonymous<'a>(call: &'a AnonymousCallExpr, nodes: &mut Vec<Node<'a>>) {
    for parameter in &call.parameters {
        collect_expression(parameter, nodes);
    }
    for input in &call.inputs {
        match input {
            AnonymousInput::Positional(value) | AnonymousInput::Named { value, .. } => {
                collect_expression(value, nodes);
            }
        }
    }
}

fn collect_expression<'a>(expression: &'a Expression, nodes: &mut Vec<Node<'a>>) {
    nodes.push(Node::Expression(expression));
    match expression {
        Expression::Name { access, .. } => {
            for part in access {
                if let Access::Index { expression, .. } = part {
                    collect_expression(expression, nodes);
                }
            }
        }
        Expression::Call { arguments, .. }
        | Expression::Array { elements: arguments, .. }
        | Expression::Tuple { elements: arguments, .. } => {
            for argument in arguments {
                collect_expression(argument, nodes);
            }
        }
        Expression::AnonymousCall(call) => collect_anonymous(call, nodes),
        Expression::Unary { operand, .. }
        | Expression::Parallel { operand, .. }
        | Expression::Group { expression: operand, .. } => collect_expression(operand, nodes),
        Expression::Binary { left, right, .. } => {
            collect_expression(left, nodes);
            collect_expression(right, nodes);
        }
        Expression::Ternary { condition, yes, no, .. } => {
            collect_expression(condition, nodes);
            collect_expression(yes, nodes);
            collect_expression(no, nodes);
        }
        Expression::Number { .. } | Expression::Error { .. } => {}
    }
}

fn check_node(node: Node<'_>, expected: &Value) -> Result<(), String> {
    if let Some(operator) = expected["operator"].as_str() {
        check_equal("operator", node_operator(node)?, operator)?;
    }
    if let Some(direction) = expected["direction"].as_str() {
        check_equal("direction", node_direction(node)?, direction)?;
    }
    if let Some(initializer) = expected["initializer"].as_str() {
        check_equal("initializer", node_initializer(node)?, initializer)?;
    }
    if let Some(modifiers) = expected["modifier"].as_str() {
        for fact in modifiers.split(';') {
            if let Some((key, value)) = fact.split_once('=') {
                check_equal(key, node_fact(node, key)?, value)?;
            } else {
                check_equal("modifier", node_simple_modifier(node)?, fact)?;
            }
        }
    }
    if let Some(shape) = expected["shape"].as_str() {
        check_equal("shape", node_shape(node)?, shape)?;
    }
    Ok(())
}

fn node_operator(node: Node<'_>) -> Result<&'static str, String> {
    match node {
        Node::Statement(Statement::Assignment { operator, .. }) => {
            Ok(assignment_operator(*operator))
        }
        Node::Statement(Statement::PostfixUpdate { operator, .. }) => {
            Ok(postfix_operator(*operator))
        }
        Node::Statement(Statement::Constraint { .. }) => Ok("==="),
        Node::Expression(Expression::Binary { operator, .. }) => Ok(binary_operator(*operator)),
        Node::Expression(Expression::Unary { operator, .. }) => Ok(unary_operator(*operator)),
        Node::Expression(Expression::AnonymousCall(call)) => named_input_operator(call),
        _ => Err("node has no operator".into()),
    }
}

fn named_input_operator(call: &AnonymousCallExpr) -> Result<&'static str, String> {
    let Some(AnonymousInput::Named { operator, .. }) = call.inputs.first() else {
        return Err("anonymous call has no named input".into());
    };
    Ok(match operator {
        InputAssignmentOperator::Assign => "assign",
        InputAssignmentOperator::Witness => "witness",
        InputAssignmentOperator::Constraint => "constraint",
    })
}

fn assignment_operator(value: AssignmentOperator) -> &'static str {
    match value {
        AssignmentOperator::Assign => "assign",
        AssignmentOperator::Witness => "witness",
        AssignmentOperator::Constraint => "constraint",
        AssignmentOperator::ReverseWitness => "reverse_witness",
        AssignmentOperator::ReverseConstraint => "reverse_constraint",
        AssignmentOperator::Add => "add",
        AssignmentOperator::Subtract => "subtract",
        AssignmentOperator::Multiply => "multiply",
        AssignmentOperator::Divide => "divide",
        AssignmentOperator::IntegerDivide => "integer_divide",
        AssignmentOperator::Modulo => "modulo",
        AssignmentOperator::Power => "power",
        AssignmentOperator::ShiftLeft => "shift_left",
        AssignmentOperator::ShiftRight => "shift_right",
        AssignmentOperator::BitAnd => "bit_and",
        AssignmentOperator::BitOr => "bit_or",
        AssignmentOperator::BitXor => "bit_xor",
    }
}

fn binary_operator(value: BinaryOperator) -> &'static str {
    match value {
        BinaryOperator::BooleanOr => "boolean_or",
        BinaryOperator::BooleanAnd => "boolean_and",
        BinaryOperator::Equal => "equal",
        BinaryOperator::NotEqual => "not_equal",
        BinaryOperator::Less => "less",
        BinaryOperator::Greater => "greater",
        BinaryOperator::LessEqual => "less_equal",
        BinaryOperator::GreaterEqual => "greater_equal",
        BinaryOperator::BitOr => "bit_or",
        BinaryOperator::BitXor => "bit_xor",
        BinaryOperator::BitAnd => "bit_and",
        BinaryOperator::ShiftLeft => "shift_left",
        BinaryOperator::ShiftRight => "shift_right",
        BinaryOperator::Add => "add",
        BinaryOperator::Subtract => "subtract",
        BinaryOperator::Multiply => "multiply",
        BinaryOperator::Divide => "divide",
        BinaryOperator::IntegerDivide => "integer_divide",
        BinaryOperator::Modulo => "modulo",
        BinaryOperator::Power => "power",
    }
}

fn unary_operator(value: UnaryOperator) -> &'static str {
    match value {
        UnaryOperator::BooleanNot => "boolean_not",
        UnaryOperator::Complement => "complement",
        UnaryOperator::Negate => "negate",
    }
}

fn postfix_operator(value: PostfixOperator) -> &'static str {
    match value {
        PostfixOperator::Increment => "increment",
        PostfixOperator::Decrement => "decrement",
    }
}

fn node_direction(node: Node<'_>) -> Result<&'static str, String> {
    let Node::Declaration(declaration) = node else {
        return Err("direction expected on declaration".into());
    };
    let direction = match &declaration.kind {
        DeclarationKind::Signal { direction, .. } | DeclarationKind::Bus { direction, .. } => {
            direction
        }
        DeclarationKind::Variable | DeclarationKind::Component => {
            return Ok("unspecified");
        }
    };
    Ok(match direction {
        DirectionSyntax::Unspecified => "unspecified",
        DirectionSyntax::Before(value) => match value.direction {
            PortDirection::Input => "input_before",
            PortDirection::Output => "output_before",
        },
        DirectionSyntax::After(value) => match value.direction {
            PortDirection::Input => "input_after",
            PortDirection::Output => "output_after",
        },
    })
}

fn node_initializer(node: Node<'_>) -> Result<String, String> {
    let Node::Declaration(declaration) = node else {
        return Err("initializer expected on declaration".into());
    };
    if let Some((operator, _)) = &declaration.tuple_initialization {
        return Ok(format!("tuple_{}", assignment_operator(*operator)));
    }
    let mut initializers =
        declaration.symbols.iter().filter_map(|symbol| symbol.initialization.as_ref());
    let Some((operator, _)) = initializers.next() else {
        return Ok("none".into());
    };
    if initializers.next().is_some() {
        return Err("multiple symbol initializers need an explicit expectation".into());
    }
    Ok(assignment_operator(*operator).into())
}

fn node_simple_modifier(node: Node<'_>) -> Result<&'static str, String> {
    match node {
        Node::Item(Item::Pragma { pragma: Pragma::Version(_), .. }) => Ok("version"),
        Node::Item(Item::Pragma { pragma: Pragma::CustomTemplates, .. }) => Ok("custom_templates"),
        Node::Trivia(Trivia { kind: TriviaKind::LineComment, .. }) => Ok("line_comment"),
        Node::Trivia(Trivia { kind: TriviaKind::BlockComment, .. }) => Ok("block_comment"),
        _ => Err("node has no simple modifier".into()),
    }
}

fn node_fact(node: Node<'_>, key: &str) -> Result<String, String> {
    match node {
        Node::Item(item) => item_fact(item, key),
        Node::Definition(definition) => definition_fact(definition, key),
        Node::Declaration(declaration) => declaration_fact(declaration, key),
        Node::Statement(statement) => statement_fact(statement, key),
        Node::Expression(expression) => expression_fact(expression, key),
        Node::Trivia(_) => Err(format!("trivia has no {key} fact")),
    }
}

fn item_fact(item: &Item, key: &str) -> Result<String, String> {
    match (item, key) {
        (Item::Main { public, .. }, "public") => {
            if public.is_empty() {
                Ok("none".into())
            } else {
                Ok(public.iter().map(|name| name.name.as_str()).collect::<Vec<_>>().join(","))
            }
        }
        _ => Err(format!("item has no {key} fact")),
    }
}

fn parentheses<T>(arguments: &ArgumentList<T>) -> &'static str {
    match arguments {
        ArgumentList::Omitted => "omitted",
        ArgumentList::Parenthesized(_) => "present",
    }
}

fn definition_fact(definition: &Definition, key: &str) -> Result<String, String> {
    match key {
        "parameters" => Ok(definition.parameters.values().len().to_string()),
        "parentheses" => Ok(parentheses(&definition.parameters).into()),
        "custom" | "external" | "parallel" => {
            let DefinitionKind::Template { custom, external, parallel } = definition.kind else {
                return Err(format!("non-template has no {key} modifier"));
            };
            let value = match key {
                "custom" => custom,
                "external" => external,
                "parallel" => parallel,
                _ => return Err(format!("unknown template modifier {key}")),
            };
            Ok(value.to_string())
        }
        _ => Err(format!("definition has no {key} fact")),
    }
}

fn declaration_fact(declaration: &Declaration, key: &str) -> Result<String, String> {
    match key {
        "symbols" => Ok(declaration.symbols.len().to_string()),
        "dims" => {
            Ok(declaration.symbols.first().map_or(0, |symbol| symbol.dimensions.len()).to_string())
        }
        "tuple" => Ok((declaration.symbol_syntax == SymbolSyntax::Tuple).to_string()),
        "tags" => match &declaration.kind {
            DeclarationKind::Signal { tags, .. } | DeclarationKind::Bus { tags, .. } => {
                Ok(tags.iter().map(|tag| tag.name.as_str()).collect::<Vec<_>>().join(","))
            }
            DeclarationKind::Variable | DeclarationKind::Component => {
                Err("non-port declaration has no tags".into())
            }
        },
        "arguments" | "parentheses" => {
            let DeclarationKind::Bus { arguments, .. } = &declaration.kind else {
                return Err("non-bus declaration has no bus arguments".into());
            };
            if key == "arguments" {
                Ok(arguments.values().len().to_string())
            } else {
                Ok(parentheses(arguments).into())
            }
        }
        _ => Err(format!("declaration has no {key} fact")),
    }
}

fn statement_fact(statement: &Statement, key: &str) -> Result<String, String> {
    match (statement, key) {
        (Statement::If { else_branch, .. }, "else") => {
            Ok(if else_branch.is_some() { "present" } else { "absent" }.into())
        }
        (Statement::For { initializer, .. }, "initializer") => Ok(match initializer.as_ref() {
            Statement::Declaration(Declaration { kind: DeclarationKind::Variable, .. }) => {
                "variable_declaration"
            }
            Statement::Assignment { .. } => "assignment",
            _ => return Err("unexpected for initializer kind".into()),
        }
        .into()),
        (Statement::Log { arguments, .. }, "arguments") => Ok(arguments.len().to_string()),
        (Statement::Log { arguments, .. }, "first") => Ok(match arguments.first() {
            Some(LogArgument::String { .. }) => "string",
            Some(LogArgument::Expression(_)) => "expression",
            None => return Err("empty log has no first argument".into()),
        }
        .into()),
        (Statement::AnonymousCall { call, .. }, "inputs") => Ok(call.inputs.len().to_string()),
        (Statement::AnonymousCall { call, .. }, "named") => Ok(inputs_named(call)?.to_string()),
        _ => Err(format!("statement has no {key} fact")),
    }
}

fn inputs_named(call: &AnonymousCallExpr) -> Result<bool, String> {
    let Some(first) = call.inputs.first() else {
        return Err("anonymous call has no inputs".into());
    };
    Ok(match first {
        AnonymousInput::Positional(_) => false,
        AnonymousInput::Named { .. } => true,
    })
}

fn expression_fact(expression: &Expression, key: &str) -> Result<String, String> {
    match (expression, key) {
        (Expression::Call { arguments, .. }, "arguments") => Ok(arguments.len().to_string()),
        (Expression::AnonymousCall(call), "inputs") => Ok(call.inputs.len().to_string()),
        (Expression::AnonymousCall(call), "named") => Ok(inputs_named(call)?.to_string()),
        (Expression::Array { elements, .. } | Expression::Tuple { elements, .. }, "elements") => {
            Ok(elements.len().to_string())
        }
        (Expression::Array { elements, .. }, "element_kind") => {
            let kinds: Vec<_> = elements
                .iter()
                .map(|element| match element {
                    Expression::Name { .. } => "name",
                    Expression::AnonymousCall(_) => "anonymous_call",
                    _ => "other",
                })
                .collect();
            if kinds.iter().all(|kind| *kind == kinds[0]) {
                Ok(kinds[0].into())
            } else {
                Ok(kinds.join(","))
            }
        }
        (Expression::Name { access, .. }, "access") => {
            if access.is_empty() {
                return Ok("none".into());
            }
            Ok(access
                .iter()
                .map(|part| match part {
                    Access::Field { .. } => "field",
                    Access::Index { .. } => "index",
                })
                .collect::<Vec<_>>()
                .join(","))
        }
        (Expression::Name { identifier, .. }, "identifier") => Ok(identifier.name.clone()),
        (Expression::Number { text, .. }, "radix") => {
            Ok(if text.starts_with("0x") { "hexadecimal" } else { "decimal" }.into())
        }
        _ => Err(format!("expression has no {key} fact")),
    }
}

fn node_shape(node: Node<'_>) -> Result<String, String> {
    match node {
        Node::Expression(expression) => expression_shape(expression),
        Node::Statement(statement) => statement_shape(statement),
        _ => Err("shape expected on expression or statement".into()),
    }
}

fn expression_shape(expression: &Expression) -> Result<String, String> {
    match expression {
        Expression::Number { text, .. } => Ok(text.clone()),
        Expression::Binary { operator, left, right, .. } => Ok(format!(
            "{}({},{})",
            binary_operator(*operator),
            expression_shape(left)?,
            expression_shape(right)?
        )),
        Expression::Ternary { condition, yes, no, .. } => Ok(format!(
            "ternary({},{},{})",
            expression_shape(condition)?,
            expression_shape(yes)?,
            expression_shape(no)?
        )),
        Expression::Group { expression, .. } => expression_shape(expression),
        _ => Err("unsupported expression in expected operator shape".into()),
    }
}

fn statement_shape(statement: &Statement) -> Result<String, String> {
    match statement {
        Statement::If { condition, then_branch, else_branch, .. } => Ok(format!(
            "if({},{},{})",
            expression_shape(condition)?,
            statement_shape(then_branch)?,
            else_branch.as_ref().map_or(Ok("none".into()), |branch| statement_shape(branch))?
        )),
        Statement::Assignment { .. } => Ok("assign".into()),
        _ => Err("unsupported statement in expected conditional shape".into()),
    }
}
