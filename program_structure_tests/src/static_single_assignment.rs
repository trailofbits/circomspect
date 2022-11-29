use std::collections::HashSet;

use parser::parse_definition;
use program_structure::cfg::{BasicBlock, Cfg, IntoCfg};
use program_structure::constants::Curve;
use program_structure::report::ReportCollection;
use program_structure::ir::variable_meta::VariableMeta;
use program_structure::ir::{AssignOp, Statement, VariableName};
use program_structure::ssa::traits::SSAStatement;

#[test]
fn test_ssa_with_array() {
    let src = r#"
        template F(x) {
            var y[2] = [0, 1];
            signal in;
            signal out;
            component c = G(y);

            y[0] += y[1] * x;
            c.in <== in + y;
            out <== c.out;
        }
    "#;
    validate_ssa(src, &["x.0", "y.0", "y.1", "in", "out", "c"]);
}

#[test]
fn test_ssa_with_components_and_signals() {
    let src = r#"
        template F(x) {
            var y = 0;
            signal in;
            signal out;
            component c = G(y);

            y += y * x;
            c.in <== in + y;
            out <== c.out;
        }
    "#;
    validate_ssa(src, &["x.0", "y.0", "y.1", "in", "out", "c"]);
}

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
    validate_ssa(src, &["x.0", "y.0", "y.1", "y.2", "y.3"]);
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
    validate_ssa(src, &["x.0", "x.1", "x.2", "x.3", "y.0", "y.1", "y.2", "y.3"]);
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
    validate_ssa(src, &["x.0", "y.0", "y.1", "y.2"]);
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
    validate_ssa(src, &["x.0", "y.0", "y.1", "y.2", "y.3"]);
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
    validate_ssa(src, &["x.0", "y.0", "y.1", "y.2", "y.3", "y.4"]);
}

#[test]
fn test_ssa_with_non_unique_variables() {
    let src = r#"
        template T(n){
            signal input in;
            signal output out[2];

            component comp[2];
            if ((n % 2) == 0) {
                for(var i = 0; i < 2; i++) {
                    comp[i].in <== in;
                }
            } else {
                for(var i = 0; i < 2; i++) {
                    out[i] <== comp[i].out;
                }
            }
        }
    "#;

    validate_ssa(
        src,
        &["n.0", "in", "out", "comp", "i.0", "i.1", "i.2", "i_0.0", "i_0.1", "i_0.2"],
    );
}
fn validate_ssa(src: &str, variables: &[&str]) {
    // 1. Generate CFG and convert to SSA.
    let mut reports = ReportCollection::new();
    let cfg = parse_definition(src)
        .unwrap()
        .into_cfg(&Curve::default(), &mut reports)
        .unwrap()
        .into_ssa()
        .unwrap();
    assert!(reports.is_empty());

    // 2. Check that each variable is assigned at most once.
    use AssignOp::*;
    use Statement::*;
    let mut assignments = HashSet::new();
    let result = cfg
        .iter()
        .flat_map(|basic_block| basic_block.iter())
        .filter_map(|stmt| match stmt {
            Substitution { var, op: AssignLocalOrComponent, .. } => Some(var),
            _ => None,
        })
        .all(|name| assignments.insert(name));
    assert!(result);

    // 3. Check that all variables are written before they are read.
    let mut env = cfg.parameters().iter().cloned().collect();
    validate_reads(cfg.entry_block(), &cfg, &mut env);

    // 4. Verify declared variables.
    assert_eq!(
        cfg.variables()
            .map(|name| format!("{:?}", name)) // Must use debug formatting here to include suffix and version.
            .collect::<HashSet<_>>(),
        variables.iter().map(|name| name.to_string()).collect::<HashSet<_>>()
    );
}

fn validate_reads(current_block: &BasicBlock, cfg: &Cfg, env: &mut HashSet<VariableName>) {
    for stmt in current_block.iter() {
        // Ignore phi function arguments as they may be generated from a loop back-edge.
        if !stmt.is_phi_statement() {
            // Check that all read variables are in the environment.
            for var_use in stmt.locals_read() {
                assert!(
                    env.contains(var_use.name()),
                    "variable `{}` is read before it is written",
                    var_use.name(),
                );
            }
        }
        // Check that no written variables are in the environment.
        for var_use in VariableMeta::locals_written(stmt) {
            assert!(
                env.insert(var_use.name().clone()),
                "variable `{}` is written multiple times",
                var_use.name(),
            );
        }
    }
    // Recurse into successors.
    for successor_block in cfg.get_dominator_successors(current_block) {
        validate_reads(successor_block, cfg, &mut env.clone());
    }
}
