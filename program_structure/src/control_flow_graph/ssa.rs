use log::debug;

use super::super::directed_graph::DirectedGraphNode;
use super::basic_block::BasicBlock;
use super::dominator_tree::DominatorTree;

use crate::ast::{Access, AssignOp, Expression, Meta, Statement};
use crate::environment::VarEnvironment;

type Index = usize;
type Version = usize;

// Insert a dummy φ statement in block j, for each variable written in block i, if j is in the
// dominance frontier of i. The variables (i.e. variable names) are still not in SSA form.
pub fn insert_phi_statements(
    basic_blocks: &mut Vec<BasicBlock>,
    dominator_tree: &DominatorTree<BasicBlock>,
) {
    // Insert φ statements at the dominance frontier of each block.
    let mut work_list: Vec<Index> = (0..basic_blocks.len()).collect();
    while let Some(current_index) = work_list.pop() {
        let variables_written = {
            let current_block = &basic_blocks[current_index];
            current_block.get_variables_written().clone()
        };
        if variables_written.is_empty() {
            debug!("basic block {current_index} does not write any variables");
            continue;
        }
        debug!(
            "dominance frontier for block {current_index} is {:?}",
            dominator_tree.get_dominance_frontier(current_index)
        );
        for frontier_index in dominator_tree.get_dominance_frontier(current_index) {
            let mut frontier_block = &mut basic_blocks[frontier_index];
            for name in &variables_written {
                if ensure_phi_statement(&mut frontier_block, &name) {
                    // If a phi statement was added to the block we need to re-add the frontier
                    // block to the work list.
                    work_list.push(frontier_index);
                }
            }
        }
    }
}

fn ensure_phi_statement(basic_block: &mut BasicBlock, name: &String) -> bool {
    if !has_phi_statement(basic_block, name) {
        debug!(
            "inserting new φ statement for variable '{name}' in block {}",
            basic_block.get_index()
        );
        let stmt = build_phi_statement(name);
        basic_block.get_statements_mut().insert(0, stmt);
        basic_block.finalize(); // Update variable use.
        return true;
    }
    false
}

fn has_phi_statement(basic_block: &BasicBlock, name: &String) -> bool {
    use Expression::Phi;
    use Statement::Substitution;
    basic_block.iter().any(|stmt| match stmt {
        Substitution {
            var,
            rhe: Phi { .. },
            ..
        } => var == name,
        _ => false,
    })
}

fn build_phi_statement(name: &String) -> Statement {
    use AssignOp::*;
    use Expression::*;
    use Statement::*;
    let phi = Phi {
        meta: Meta::new(0, 0),
        // φ expression arguments are added later.
        args: Vec::new(),
    };
    Substitution {
        meta: Meta::new(0, 0),
        var: name.clone(),
        op: AssignVar,
        rhe: phi,
        access: Vec::new(),
    }
}

// Update the RHS of each φ statement in the basic block with the SSA variable
// versions from the given environment. The LHS will be updated when this basic
// block is reached in the dominance tree.
fn update_phi_statements(basic_block: &mut BasicBlock, env: &VarEnvironment<Version>) {
    use Expression::{Phi, SSAVariable};
    use Statement::Substitution;
    debug!(
        "updating φ expression arguments in block {}",
        basic_block.get_index()
    );
    basic_block.iter_mut().for_each(|stmt| {
        match stmt {
            // φ statement found.
            Substitution {
                var: name,
                rhe: Phi { args, .. },
                ..
            } => {
                debug!("φ statement for variable '{name}' found");
                if let Some(version) = env.get_variable(name) {
                    // If the argument list does not contain the SSA variable we add it.
                    if args.iter().all(|arg| {
                        !matches!(
                            arg,
                            SSAVariable {
                                name: n,
                                version: v,
                                ..
                            } if n == name && v == version
                        )
                    }) {
                        args.push(SSAVariable {
                            meta: Meta::new(0, 0),
                            name: name.clone(),
                            access: Vec::new(),
                            version: version.clone(),
                        });
                    }
                }
            }
            _ => {
                // Since φ statements proceed all other statements we are done here.
                return;
            }
        }
    });
}

pub fn insert_ssa_variables(
    basic_blocks: &mut Vec<BasicBlock>,
    dominator_tree: &DominatorTree<BasicBlock>,
) {
    let mut env = VarEnvironment::new();
    insert_ssa_variables_impl(0, basic_blocks, dominator_tree, &mut env);
}

fn insert_ssa_variables_impl(
    current_index: Index,
    basic_blocks: &mut Vec<BasicBlock>,
    dominator_tree: &DominatorTree<BasicBlock>,
    env: &mut VarEnvironment<Version>,
) {
    // 1. Update variables in current block.
    let successors = {
        let current_block = basic_blocks
            .get_mut(current_index)
            .expect("invalid block index during SSA generation");
        *current_block = visit_basic_block(current_block, env);
        current_block.get_successors().clone()
    };

    // 2. Update phi statements in successor blocks.
    for successor_index in successors {
        let successor_block = basic_blocks
            .get_mut(successor_index)
            .expect("invalid block index during SSA generation");
        update_phi_statements(successor_block, env);
    }
    // 3. Update dominator tree successors recursively.
    for successor_index in dominator_tree.get_dominator_successors(current_index) {
        insert_ssa_variables_impl(
            successor_index,
            basic_blocks,
            dominator_tree,
            &mut env.clone(),
        );
    }
}

fn visit_basic_block(basic_block: &BasicBlock, env: &mut VarEnvironment<Version>) -> BasicBlock {
    debug!(
        "renaming variables to SSA form in block {}",
        basic_block.get_index()
    );
    let mut stmts: Vec<Statement> = Vec::new();
    for stmt in basic_block.get_statements() {
        stmts.extend(visit_statement(stmt, env))
    }
    let mut basic_block = BasicBlock::from_raw_parts(
        basic_block.get_index(),
        basic_block.get_meta().clone(),
        stmts,
        basic_block.get_predecessors().clone(),
        basic_block.get_successors().clone(),
    );
    basic_block.finalize();
    basic_block
}

fn visit_statement(stmt: &Statement, env: &mut VarEnvironment<Version>) -> Vec<Statement> {
    use Statement::*;
    match stmt {
        IfThenElse {
            meta,
            cond,
            if_case,
            else_case,
        } => {
            let if_case = Box::new(build_empty_block(if_case.get_meta().to_owned()));
            let else_case = match else_case {
                Some(stmt) => Some(Box::new(build_empty_block((*stmt).get_meta().clone()))),
                None => None,
            };
            vec![IfThenElse {
                meta: meta.clone(),
                cond: visit_expression(cond, env),
                if_case,
                else_case,
            }]
        }
        While { meta, cond, stmt } => {
            vec![While {
                meta: meta.clone(),
                cond: visit_expression(cond, env),
                stmt: Box::new(build_empty_block(stmt.get_meta().to_owned())),
            }]
        }
        Return { meta, value } => {
            vec![Return {
                meta: meta.clone(),
                value: visit_expression(value, env),
            }]
        }
        Declaration { .. } => {
            // TODO: This goes away after conversion to IR.
            Vec::new()
        }
        Substitution {
            meta,
            var,
            access,
            op,
            rhe,
        } => {
            // If this is the first assignment to the variable we set the version to 0.
            let version = env
                .get_variable(&var)
                .map(|&version| version + 1)
                .unwrap_or(0);
            env.add_variable(&var, version);
            let ssa_var = format!(
                "{}",
                build_ssa_variable(meta.clone(), var.to_string(), Vec::new(), version)
            );
            debug!("replacing (written) variable '{var}' with SSA variable '{ssa_var}'");
            vec![Substitution {
                meta: meta.clone(),
                var: ssa_var,
                access: access.clone(),
                op: op.clone(),
                rhe: visit_expression(rhe, env),
            }]
        }
        ConstraintEquality { meta, lhe, rhe } => {
            vec![ConstraintEquality {
                meta: meta.clone(),
                lhe: visit_expression(lhe, env),
                rhe: visit_expression(rhe, env),
            }]
        }
        LogCall { meta, arg } => {
            vec![LogCall {
                meta: meta.clone(),
                arg: visit_expression(arg, env),
            }]
        }
        Assert { meta, arg } => {
            vec![Assert {
                meta: meta.clone(),
                arg: visit_expression(arg, env),
            }]
        }
        InitializationBlock { .. } | Block { .. } => {
            // TODO: This goes away after conversion to IR.
            unreachable!("unexpected statement type ({:?})", stmt)
        }
    }
}

fn visit_expression(expr: &Expression, env: &VarEnvironment<Version>) -> Expression {
    use Expression::*;
    match expr {
        InfixOp {
            meta,
            lhe,
            infix_op,
            rhe,
        } => InfixOp {
            meta: meta.clone(),
            lhe: Box::new(visit_expression(lhe.as_ref(), env)),
            infix_op: infix_op.clone(),
            rhe: Box::new(visit_expression(rhe.as_ref(), env)),
        },
        PrefixOp {
            meta,
            prefix_op,
            rhe,
        } => PrefixOp {
            meta: meta.clone(),
            prefix_op: prefix_op.clone(),
            rhe: Box::new(visit_expression(rhe, env)),
        },
        InlineSwitchOp {
            meta,
            cond,
            if_true,
            if_false,
        } => InlineSwitchOp {
            meta: meta.clone(),
            cond: Box::new(visit_expression(cond, env)),
            if_true: Box::new(visit_expression(if_true, env)),
            if_false: Box::new(visit_expression(if_false, env)),
        },
        Variable { meta, name, access } => {
            let version = env.get_variable(&name).copied().unwrap_or_default();
            let ssa_var = SSAVariable {
                meta: meta.clone(),
                name: name.clone(),
                access: access.clone(),
                version,
            };
            debug!("replacing (read) variable '{name}' with SSA variable '{ssa_var}'");
            ssa_var
        }
        SSAVariable { .. } => {
            unreachable!("variable already converted to SSA form")
        }
        Number(meta, value) => Number(meta.clone(), value.clone()),
        Call { meta, id, args } => {
            let args = args
                .into_iter()
                .map(|expr| visit_expression(expr, env))
                .collect();
            Call {
                meta: meta.clone(),
                id: id.clone(),
                args,
            }
        }
        ArrayInLine { meta, values } => {
            let values = values
                .into_iter()
                .map(|expr| visit_expression(expr, env))
                .collect();
            ArrayInLine {
                meta: meta.clone(),
                values,
            }
        }
        Phi { meta, args } => {
            // φ expression arguments are updated in a later pass.
            Phi {
                meta: meta.clone(),
                args: args.clone(),
            }
        }
    }
}

fn build_ssa_variable(meta: Meta, name: String, access: Vec<Access>, version: usize) -> Expression {
    use Expression::*;
    SSAVariable {
        meta,
        name,
        access,
        version,
    }
}

fn build_empty_block(meta: Meta) -> Statement {
    use Statement::*;
    Block {
        meta,
        stmts: Vec::new(),
    }
}
