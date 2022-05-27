use std::collections::HashSet;

use parser::parse_definition;
use program_structure::cfg::*;

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
        &[3, 2, 1],
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
        &[3, 2, 2, 1],
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
        &[2, 1, 1, 1],
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
        &[3, 2, 1, 1],
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
        &[2, 1, 1, 1, 1, 1],
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

fn validate_cfg(src: &str, lengths: &[usize], edges: &[(Vec<Index>, Vec<Index>)]) {
    // 1. Generate CFG from source.
    let (cfg, _) = parse_definition(src).unwrap().try_into().unwrap();

    // 2. Validate block lengths.
    for (basic_block, length) in cfg.iter().zip(lengths.iter()) {
        assert_eq!(basic_block.len(), *length);
    }

    // 3. Validate block edges against input.
    for (basic_block, edges) in cfg.iter().zip(edges.iter()) {
        let actual_predecessors = basic_block.get_predecessors();
        let expected_predecessors: HashSet<_> = edges.0.iter().cloned().collect();
        assert_eq!(
            actual_predecessors,
            &expected_predecessors,
            "unexpected predecessor set for block {}",
            basic_block.get_index()
        );

        let actual_successors = basic_block.get_successors();
        let expected_successors: HashSet<_> = edges.1.iter().cloned().collect();
        assert_eq!(
            actual_successors,
            &expected_successors,
            "unexpected successor set for block {}",
            basic_block.get_index()
        );
    }

    // 4. Check that block j is a successor of i iff i is a predecessor of j.
    for first_block in cfg.iter() {
        for second_block in cfg.iter() {
            assert_eq!(
                first_block
                    .get_successors()
                    .contains(&second_block.get_index()),
                second_block
                    .get_predecessors()
                    .contains(&first_block.get_index()),
                "basic block {} is not a predecessor of a successor block {}",
                first_block.get_index(),
                second_block.get_index()
            );
        }
    }
}
