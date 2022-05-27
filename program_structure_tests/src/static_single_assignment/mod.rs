use std::collections::HashSet;

use parser::parse_definition;
use program_structure::cfg::basic_block::BasicBlock;
use program_structure::cfg::Cfg;
use program_structure::ir::variable_meta::VariableMeta;
use program_structure::ir::{AssignOp, Statement, VariableName};
use program_structure::ssa::traits::SSAStatement;

#[test]
fn test_ssa_from_if() {
    let src = r#"
        function f(x) {
            var y = 0;
            if (x > 0) {
                y = x;
                y += y * x;
            }
            return y + x;
        }
    "#;
    validate_ssa(src);
}

#[test]
fn test_ssa_from_if_then_else() {
    let src = r#"
        function f(x) {
            var y = 0;
            if (x > 0) {
                y = x;
                y += y * x;
            } else {
                x = y;
                x += x + 1;
            }
            return y + x;
        }
    "#;
    validate_ssa(src);
}

#[test]
fn test_ssa_from_while() {
    let src = r#"
        function f(x) {
            var y = 0;
            while (y < x) {
                y += y ** 2 + 1;
            }
            return y + x;
        }
    "#;
    validate_ssa(&src);
}

#[test]
fn test_ssa_from_nested_if() {
    let src = r#"
        function f(x) {
            var y = 0;
            if (y <= x) {
                y *= 2;
                if (y == x) {
                    y *= 2;
                }
            }
            return y + x;
        }
    "#;
    validate_ssa(&src);
}

#[test]
fn test_ssa_from_nested_while() {
    let src = r#"
        function f(x) {
            var y = 0;
            while (y <= x) {
                y *= 2;
                while (y < x) {
                    y *= 2;
                }
            }
            return y + x;
        }
    "#;
    validate_ssa(&src);
}

fn validate_ssa(src: &str) {
    // 1. Generate CFG and convert to SSA.
    let (mut cfg, _) = parse_definition(src).unwrap().try_into().unwrap();
    cfg.into_ssa().unwrap();

    // 2. Check that each variable is assigned at most once.
    use AssignOp::*;
    use Statement::*;
    let mut assignments = HashSet::new();
    let result = cfg
        .iter()
        .flat_map(|basic_block| basic_block.iter())
        .filter_map(|stmt| match stmt {
            Substitution {
                var, op: AssignVar, ..
            } => Some(var),
            _ => None,
        })
        .all(|name| assignments.insert(name));
    assert!(result);

    // 3. Check that all variables are written before they are read.
    let mut env = cfg.get_parameters().iter().cloned().collect();
    validate_reads(cfg.get_entry_block(), &cfg, &mut env);
}

fn validate_reads(current_block: &BasicBlock, cfg: &Cfg, env: &mut HashSet<VariableName>) {
    for stmt in current_block.iter() {
        // Ignore phi function arguments as they may be generated from a loop back-edge.
        if !stmt.is_phi_statement() {
            // Check that all read variables are in the environment.
            for name in stmt.get_variables_read() {
                assert!(
                    env.contains(name),
                    "variable `{name}` is read before it is written"
                );
            }
        }
        // Check that no written variables are in the environment.
        for name in VariableMeta::get_variables_written(stmt) {
            assert!(
                env.insert(name.clone()),
                "variable `{name}` is written multiple times {stmt}"
            );
        }
    }
    // Recurse into successors.
    for successor_block in cfg.get_dominator_successors(&current_block) {
        validate_reads(successor_block, cfg, &mut env.clone());
    }
}
