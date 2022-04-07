use std::collections::HashSet;

type Index = usize;

// This trait is used to make graph algorithms (like dominator tree and dominator
// frontier generation) generic of the graph node type for unit testing purposes.
pub trait DirectedGraphNode {
    fn get_index(&self) -> Index;

    fn get_predecessors(&self) -> &HashSet<Index>;

    fn get_successors(&self) -> &HashSet<Index>;
}
