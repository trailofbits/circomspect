use std::collections::{HashMap, HashSet};

use parser::parse_definition;
use program_structure::cfg::*;
use program_structure::constants::Curve;
use program_structure::report::ReportCollection;
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
        &[3, 2, 1],
        &[(vec![], vec![1, 2]), (vec![0], vec![2]), (vec![0, 1], vec![])],
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
        &[3, 2, 2, 1],
        &[(vec![], vec![1, 2]), (vec![0], vec![3]), (vec![0], vec![3]), (vec![1, 2], vec![])],
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
        &["x", "y"],
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
        &["x", "y"],
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

#[test]
fn test_cfg_with_non_unique_variables() {
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

    validate_cfg(
        src,
        &["n", "in", "out", "comp", "i", "i.0"],
        &[4, 2, 1, 2, 2, 1, 2],
        &[
            (vec![], vec![1, 4]),
            // 0:
            // signal input in;
            // signal output out[2];
            // component comp[2];
            // if ((n % 2) == 0)
            (vec![0], vec![2]),
            //   1:
            //   var i;
            //   i = 0;
            (vec![1, 3], vec![3]),
            //   2:
            //   if (i < 2)
            (vec![2], vec![2]),
            //     3:
            //     comp[i].in = in;
            //     i++;
            (vec![0], vec![5]),
            //   4:
            //   var i_0;
            //   i_0 = 0;
            (vec![4, 6], vec![6]),
            //   5:
            //   if (i_0 < 2)
            (vec![5], vec![5]),
            //     6:
            //     out[i] <== comp[i_0].out;
            //     i_0++;
        ],
    );
}

#[test]
fn test_dominance_from_nested_if() {
    // 0:
    // var y;
    // y = 0;
    // if (y <= 0)
    //
    //   1:
    //   y *= 2;
    //   if (y == x)
    //
    //     2:
    //     y *= 2;
    //
    // 3:
    // return y + x;
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

    let mut immediate_dominators = HashMap::new();
    immediate_dominators.insert(0, None);
    immediate_dominators.insert(1, Some(0));
    immediate_dominators.insert(2, Some(1));
    immediate_dominators.insert(3, Some(0));

    let mut dominance_frontier = HashMap::new();
    dominance_frontier.insert(0, HashSet::new());
    dominance_frontier.insert(1, HashSet::from([3]));
    dominance_frontier.insert(2, HashSet::from([3]));
    dominance_frontier.insert(3, HashSet::new());

    validate_dominance(&src, &immediate_dominators, &dominance_frontier);
}

#[test]
fn test_dominance_from_nested_if_then_else() {
    // 0:
    // var y;
    // y = 2;
    // if (x > 0)
    //
    //   1:
    //   return x * y;
    //
    //   2:
    //   if (x < 0)
    //
    //     3:
    //     return x - y;
    //
    //     4:
    //     return y;
    let src = r#"
        function f(x) {
            var y = 2;
            if (x > 0) {
                return x * y;
            } else {
                if (x < 0) {
                    return x - y;
                } else {
                    return y;
                }
            }
        }
    "#;

    let mut immediate_dominators = HashMap::new();
    immediate_dominators.insert(0, None);
    immediate_dominators.insert(1, Some(0));
    immediate_dominators.insert(2, Some(0));
    immediate_dominators.insert(3, Some(2));
    immediate_dominators.insert(4, Some(2));

    let mut dominance_frontier = HashMap::new();
    dominance_frontier.insert(0, HashSet::new());
    dominance_frontier.insert(1, HashSet::new());
    dominance_frontier.insert(2, HashSet::new());
    dominance_frontier.insert(3, HashSet::new());

    validate_dominance(&src, &immediate_dominators, &dominance_frontier);
}

#[test]
fn test_branches_from_nested_if_then_else() {
    // 0:
    // var y;
    // y = 2;
    // if (x > 0)
    //
    //   1:
    //   return x * y;
    //
    //   2:
    //   if (x < 0)
    //
    //     3:
    //     return x - y;
    //
    //     4:
    //     return y;
    let src = r#"
        function f(x) {
            var y = 2;
            if (x > 0) {
                return x * y;
            } else {
                if (x < 0) {
                    return x - y;
                } else {
                    return y;
                }
            }
        }
    "#;

    let mut true_branches = HashMap::new();
    true_branches.insert(0, HashSet::from([1]));
    true_branches.insert(2, HashSet::from([3]));

    let mut false_branches = HashMap::new();
    false_branches.insert(0, HashSet::from([2, 3, 4]));
    false_branches.insert(2, HashSet::from([4]));

    validate_branches(&src, &true_branches, &false_branches);
}

#[test]
fn test_branches_from_nested_if() {
    // 0:
    // var y;
    // y = 0;
    // if (y <= 0)
    //
    //   1:
    //   y *= 2;
    //   if (y == x)
    //
    //     2:
    //     y *= 2;
    //
    // 3:
    // return y + x;
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

    let mut true_branches = HashMap::new();
    true_branches.insert(0, HashSet::from([1, 2]));
    true_branches.insert(1, HashSet::from([2]));

    let mut false_branches = HashMap::new();
    false_branches.insert(0, HashSet::new());
    false_branches.insert(1, HashSet::new());

    validate_branches(&src, &true_branches, &false_branches);
}

fn validate_cfg(
    src: &str,
    variables: &[&str],
    lengths: &[usize],
    edges: &[(Vec<Index>, Vec<Index>)],
) {
    // 1. Generate CFG from source.
    let mut reports = ReportCollection::new();
    let cfg = parse_definition(src).unwrap().into_cfg(&Curve::default(), &mut reports).unwrap();
    assert!(reports.is_empty());

    // 2. Verify declared variables.
    assert_eq!(
        cfg.variables().cloned().collect::<HashSet<_>>(),
        variables.iter().map(|name| lift(name)).collect::<HashSet<_>>()
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
                first_block.successors().contains(&second_block.index()),
                second_block.predecessors().contains(&first_block.index()),
                "basic block {} is not a predecessor of a successor block {}",
                first_block.index(),
                second_block.index()
            );
        }
    }
}

fn validate_dominance(
    src: &str,
    immediate_dominators: &HashMap<usize, Option<usize>>,
    dominance_frontier: &HashMap<usize, HashSet<usize>>,
) {
    // 1. Generate CFG from source.
    let mut reports = ReportCollection::new();
    let cfg = parse_definition(src).unwrap().into_cfg(&Curve::default(), &mut reports).unwrap();
    assert!(reports.is_empty());

    // 2. Validate immediate dominators.
    for (index, expected_dominator) in immediate_dominators {
        let basic_block = cfg.get_basic_block(*index).unwrap();
        let immediate_dominator =
            cfg.get_immediate_dominator(basic_block).map(|dominator_block| dominator_block.index());
        assert_eq!(&immediate_dominator, expected_dominator);
    }

    // 3. Validate dominance frontier.
    for (index, expected_frontier) in dominance_frontier {
        let basic_block = cfg.get_basic_block(*index).unwrap();
        let dominance_frontier = cfg
            .get_dominance_frontier(basic_block)
            .iter()
            .map(|frontier_block| frontier_block.index())
            .collect::<HashSet<_>>();
        assert_eq!(&dominance_frontier, expected_frontier);
    }
}

fn validate_branches(
    src: &str,
    true_branches: &HashMap<usize, HashSet<usize>>,
    false_branches: &HashMap<usize, HashSet<usize>>,
) {
    // 1. Generate CFG from source.
    let mut reports = ReportCollection::new();
    let cfg = parse_definition(src).unwrap().into_cfg(&Curve::default(), &mut reports).unwrap();
    assert!(reports.is_empty());

    // 2. Validate the set of true branches.
    for (header_index, expected_indices) in true_branches {
        let header_block = cfg.get_basic_block(*header_index).unwrap();
        let true_branch = cfg.get_true_branch(header_block);
        let true_indices =
            true_branch.iter().map(|basic_block| basic_block.index()).collect::<HashSet<_>>();
        assert_eq!(&true_indices, expected_indices);
    }

    // 3. Validate the set of false branches.
    for (header_index, expected_indices) in false_branches {
        let header_block = cfg.get_basic_block(*header_index).unwrap();
        let false_branch = cfg.get_false_branch(header_block);
        let false_indices =
            false_branch.iter().map(|basic_block| basic_block.index()).collect::<HashSet<_>>();
        assert_eq!(&false_indices, expected_indices);
    }
}

fn lift(name: &str) -> VariableName {
    // We assume that the input string uses '.' to separate the name from the suffix.
    let tokens: Vec<_> = name.split('.').collect();
    match tokens.len() {
        1 => VariableName::from_name(tokens[0]),
        2 => VariableName::from_name(tokens[0]).with_suffix(tokens[1]),
        _ => panic!("invalid variable name"),
    }
}
