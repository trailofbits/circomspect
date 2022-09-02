use log::trace;
use std::collections::HashSet;
use std::marker::PhantomData;

use super::traits::DirectedGraphNode;

type Index = usize;
type DominatorInfo = Vec<HashSet<Index>>;
type ImmediateDominatorInfo = Vec<Option<Index>>;

// A structure which encapsulates the dominance relation on a CFG.
pub struct DominatorTree<T: DirectedGraphNode> {
    dominators: DominatorInfo,
    immediate_dominators: ImmediateDominatorInfo,
    dominator_successors: DominatorInfo,
    dominance_frontier: DominatorInfo,
    marker: PhantomData<T>,
}

impl<T: DirectedGraphNode> DominatorTree<T> {
    pub fn new(basic_blocks: &[T]) -> DominatorTree<T> {
        let dominators = compute_dominators(basic_blocks);
        let (immediate_dominators, dominator_successors) =
            compute_immediate_dominators(basic_blocks, &dominators);
        let dominance_frontier = compute_dominance_frontier(basic_blocks, &immediate_dominators);
        // We assume that the first block (with index 0) represents the entry block.
        assert!(immediate_dominators[0].is_none());
        DominatorTree {
            dominators,
            immediate_dominators,
            dominator_successors,
            dominance_frontier,
            marker: PhantomData::default(),
        }
    }

    pub fn get_entry_block(&self) -> Index {
        Index::default()
    }

    pub fn get_dominators(&self, i: Index) -> HashSet<Index> {
        self.dominators[i].clone()
    }

    pub fn get_immediate_dominator(&self, i: Index) -> Option<Index> {
        self.immediate_dominators[i]
    }

    pub fn get_dominator_successors(&self, i: Index) -> HashSet<Index> {
        self.dominator_successors[i].clone()
    }

    pub fn get_dominance_frontier(&self, i: Index) -> HashSet<Index> {
        self.dominance_frontier[i].clone()
    }
}

// This is a stupid simple (quadratic) algorithm based on an iterative data-flow analysis.
fn compute_dominators<T: DirectedGraphNode>(basic_blocks: &[T]) -> DominatorInfo {
    let mut dominators = Vec::new();
    let nof_blocks = basic_blocks.len();
    dominators.push(HashSet::from([0]));
    for _ in 1..basic_blocks.len() {
        dominators.push((0..nof_blocks).collect());
    }

    let mut done = false;
    while !done {
        done = true;
        for i in 1..nof_blocks {
            let mut new_dominators: HashSet<usize> = (0..nof_blocks).collect();
            for &j in basic_blocks[i].predecessors() {
                new_dominators = new_dominators.intersection(&dominators[j]).copied().collect();
            }
            new_dominators.insert(i);
            if new_dominators != dominators[i] {
                dominators[i] = new_dominators;
                done = false;
            }
        }
    }
    dominators
}

// Compute immediate dominators (a `Vec<Option<usize>>`) and the dominator tree relation (a
// `Vec<HashSet<usize>>`). (Note that the entry block of the CFG has no immediate dominator.)
fn compute_immediate_dominators<T: DirectedGraphNode>(
    basic_blocks: &[T],
    dominators: &DominatorInfo,
) -> (ImmediateDominatorInfo, DominatorInfo) {
    let nof_blocks = basic_blocks.len();
    let mut immediate_dominators = vec![None; nof_blocks];
    let mut dominator_successors = vec![HashSet::new(); nof_blocks];

    for i in 0..nof_blocks {
        trace!("the dominator set of block {i} is {:?}", dominators[i]);
        let mut idom_candidates: HashSet<usize> = dominators[i].clone();
        idom_candidates.remove(&i);

        if idom_candidates.len() > 1 {
            // The set `all_dominators` is the strict up set of the nodes dominators. I.e.
            //
            //     `all_dominators(i) = U {Dom(j) - {j}; j strictly dominates i}`.
            //
            // The immediate dominator of the node will be the unique element in the set
            // `idom_candidates - all_dominators` when this set is non-empty.
            let mut all_dominators: HashSet<usize> = HashSet::new();
            for j in &idom_candidates {
                // 'all_dominators' is upwards closed.
                if all_dominators.contains(j) {
                    continue;
                }
                // Set `all_dominators = all_dominators U (Dom(i) \ {i}`.
                all_dominators = dominators[*j]
                    .clone()
                    .into_iter()
                    .filter(|&k| k != *j) // Remove i.
                    .collect::<HashSet<usize>>()
                    .union(&all_dominators)
                    .copied()
                    .collect();
            }
            idom_candidates = &idom_candidates - &all_dominators;
            assert!(idom_candidates.len() <= 1);
        }
        if let Some(&j) = idom_candidates.iter().next() {
            trace!("the immediate dominator of {i} is {j}");
            immediate_dominators[i] = Some(j);
            dominator_successors[j].insert(i);
        }
    }
    (immediate_dominators, dominator_successors)
}

// Compute dominance frontiers (a `Vec<HashSet<usize>>`) of all nodes. The node
// `i` is in the _dominance frontier_ of the node `j` if `j` dominates an
// immediate predecessor of `i`, but `j` does not strictly dominate `i`.
fn compute_dominance_frontier<T: DirectedGraphNode>(
    basic_blocks: &[T],
    immediate_dominators: &ImmediateDominatorInfo,
) -> DominatorInfo {
    let nof_blocks = basic_blocks.len();
    let mut dominance_frontier = vec![HashSet::new(); nof_blocks];
    for i in 0..nof_blocks {
        if basic_blocks[i].predecessors().len() > 1 {
            for &j in basic_blocks[i].predecessors() {
                let mut k = j;
                while Some(k) != immediate_dominators[i] {
                    dominance_frontier[k].insert(i);
                    k = match immediate_dominators[k] {
                        Some(idom) => idom,
                        None => break,
                    };
                }
            }
        }
    }
    dominance_frontier
}
