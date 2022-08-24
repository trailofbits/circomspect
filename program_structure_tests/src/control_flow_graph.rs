use std::collections::HashSet;

use parser::parse_definition;
use program_structure::cfg::*;
use program_structure::error_definition::ReportCollection;
use program_structure::ir::VariableName;

#[test]
fn test_cfg_from_if() {
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
    validate_cfg(
        src,
        &["x", "y"],
        &[2, 2, 1],
        &[
            (vec![], vec![1, 2]),
            (vec![0], vec![2]),
            (vec![0, 1], vec![]),
        ],
    );
}

#[test]
fn test_cfg_from_if_then_else() {
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
    validate_cfg(
        src,
        &["x", "y"],
        &[2, 2, 2, 1],
        &[
            (vec![], vec![1, 2]),
            (vec![0], vec![3]),
            (vec![0], vec![3]),
            (vec![1, 2], vec![]),
        ],
    );
}

#[test]
fn test_cfg_from_while() {
    let src = r#"
        function f(x) {
            var y = 0;
            while (y < x) {
                y += y ** 2 + 1;
            }
            return y + x;
        }
    "#;
    validate_cfg(
        src,
        &["x", "y"],
        &[1, 1, 1, 1],
        &[
            (vec![], vec![1]),
            // 0:
            // var y;
            // y = 0;
            (vec![0, 2], vec![2, 3]),
            // 1:
            // if (y < 0)
            (vec![1], vec![1]),
            //   2:
            //   y += y ** 2 + 1
            (vec![1], vec![]),
            // 3:
            // return y + x;
        ],
    );
}

#[test]
fn test_cfg_from_nested_if() {
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
    validate_cfg(
        src,
        &["x", "y"],
        &[2, 2, 1, 1],
        &[
            (vec![], vec![1, 3]),
            // 0:
            // var y;
            // y = 0;
            // if (y <= 0)
            (vec![0], vec![2, 3]),
            //   1:
            //   y *= 2;
            //   if (y == x)
            (vec![1], vec![3]),
            //     2:
            //     y *= 2;
            (vec![0, 1, 2], vec![]),
            // 3:
            // return y + x;
        ],
    );
}

#[test]
fn test_cfg_from_nested_while() {
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
    validate_cfg(
        src,
        &["x", "y"],
        &[1, 1, 1, 1, 1, 1],
        &[
            (vec![], vec![1]),
            // 0:
            // var y;
            // y = 0;
            (vec![0, 3], vec![2, 5]),
            // 1:
            // if (y <= 0)
            (vec![1], vec![3]),
            //   2:
            //   y *= 2;
            (vec![2, 4], vec![4, 1]),
            //   3:
            //   if (y < x)
            (vec![3], vec![3]),
            //     4:
            //     y *= 2;
            (vec![1], vec![]),
            // 5:
            // return y + x;
        ],
    );
}

fn validate_cfg(
    src: &str,
    variables: &[&str],
    lengths: &[usize],
    edges: &[(Vec<Index>, Vec<Index>)],
) {
    // 1. Generate CFG from source.
    let mut reports = ReportCollection::new();
    let cfg = parse_definition(src).unwrap().into_cfg(&mut reports).unwrap();

    // 2. Verify declared variables.
    assert_eq!(
        cfg.variables().cloned().collect::<HashSet<_>>(),
        variables
            .iter()
            .map(|name| VariableName::from_name(name))
            .collect::<HashSet<_>>()
    );

    // 3. Validate block lengths.
    for (basic_block, length) in cfg.iter().zip(lengths.iter()) {
        assert_eq!(basic_block.len(), *length);
    }

    // 4. Validate block edges against input.
    for (basic_block, edges) in cfg.iter().zip(edges.iter()) {
        let actual_predecessors = basic_block.predecessors();
        let expected_predecessors: HashSet<_> = edges.0.iter().cloned().collect();
        assert_eq!(
            actual_predecessors,
            &expected_predecessors,
            "unexpected predecessor set for block {}",
            basic_block.index()
        );

        let actual_successors = basic_block.successors();
        let expected_successors: HashSet<_> = edges.1.iter().cloned().collect();
        assert_eq!(
            actual_successors,
            &expected_successors,
            "unexpected successor set for block {}",
            basic_block.index()
        );
    }

    // 5. Check that block j is a successor of i iff i is a predecessor of j.
    for first_block in cfg.iter() {
        for second_block in cfg.iter() {
            assert_eq!(
                first_block
                    .successors()
                    .contains(&second_block.index()),
                second_block
                    .predecessors()
                    .contains(&first_block.index()),
                "basic block {} is not a predecessor of a successor block {}",
                first_block.index(),
                second_block.index()
            );
        }
    }
}
