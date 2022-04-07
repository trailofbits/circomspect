use log::{debug, warn};
use std::collections::HashSet;

use super::variable_use::compute_variable_use;
use crate::abstract_syntax_tree::ast::{Meta, Statement};
use crate::utils::directed_graph::DirectedGraphNode;

type Index = usize;

#[derive(Clone)]
pub struct BasicBlock {
    index: Index,
    meta: Meta,
    stmts: Vec<Statement>,
    predecessors: HashSet<Index>,
    successors: HashSet<Index>,
}

impl Default for BasicBlock {
    fn default() -> BasicBlock {
        BasicBlock {
            index: 0,
            meta: Meta::new(0, 0),
            stmts: Vec::default(),
            predecessors: HashSet::default(),
            successors: HashSet::default(),
        }
    }
}

impl BasicBlock {
    // Create a new basic block with the given block as predecessor. The index
    // of the new block will be `predecessor.get_index() + 1`. The predecessor
    // block is updated by adding the new block as a successor.
    pub(crate) fn with_predecessor(predecessor: &mut BasicBlock) -> BasicBlock {
        let index = predecessor.index + 1;
        debug!(
            "creating basic block {index} with predecessor {}",
            predecessor.index
        );
        let mut basic_block = BasicBlock {
            index,
            ..Default::default()
        };
        predecessor.add_successor(&basic_block);
        basic_block.add_predecessor(predecessor);
        basic_block
    }

    pub(crate) fn from_raw_parts(
        index: Index,
        meta: Meta,
        stmts: Vec<Statement>,
        predecessors: HashSet<Index>,
        successors: HashSet<Index>,
    ) -> BasicBlock {
        BasicBlock {
            index,
            meta,
            stmts,
            predecessors,
            successors,
        }
    }

    // Replace left and right block indices with the new block index in all block successor sets
    // Compute the new predecessor set as the union of the left and right predecessor sets.
    pub(crate) fn merge(
        left_block: BasicBlock,
        right_block: BasicBlock,
        basic_blocks: &mut [BasicBlock],
    ) -> BasicBlock {
        let index = basic_blocks.len();
        let mut predecessors = HashSet::new();
        left_block.predecessors.iter().for_each(|&i| {
            basic_blocks[i]
                .get_successors_mut()
                .remove(&left_block.index);
            basic_blocks[i].get_successors_mut().insert(index);
            predecessors.insert(i);
        });
        right_block.predecessors.iter().for_each(|&i| {
            basic_blocks[i]
                .get_successors_mut()
                .remove(&right_block.index);
            basic_blocks[i].get_successors_mut().insert(index);
            predecessors.insert(i);
        });
        BasicBlock {
            index,
            predecessors,
            ..Default::default()
        }
    }

    // Update meta with location and variable knowledge.
    pub(crate) fn finalize(&mut self) -> &mut BasicBlock {
        // Update location.
        let start = self
            .stmts
            .first()
            .map(|stmt| stmt.get_meta().get_start())
            .unwrap_or_default();
        let end = self
            .stmts
            .last()
            .map(|stmt| stmt.get_meta().get_end())
            .unwrap_or_default();
        self.meta.change_location(start..end, None);

        // Cache variable knowledge.
        let mut variables_read = HashSet::new();
        let mut variables_written = HashSet::new();
        for mut stmt in self.get_statements_mut() {
            compute_variable_use(&mut stmt);
            let update_read = stmt
                .get_meta()
                .get_variable_knowledge()
                .get_variables_read()
                .iter()
                .cloned();
            variables_read.extend(update_read);
            let update_written = stmt
                .get_meta()
                .get_variable_knowledge()
                .get_variables_written()
                .iter()
                .cloned();
            variables_written.extend(update_written);
        }
        let variable_knowledge = self.get_mut_meta().get_mut_variable_knowledge();
        variable_knowledge.set_variables_read(&variables_read);
        variable_knowledge.set_variables_written(&variables_written);
        self
    }

    pub fn len(&self) -> usize {
        self.stmts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() > 0
    }

    pub fn iter(&self) -> impl Iterator<Item = &Statement> {
        self.stmts.iter()
    }

    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = &mut Statement> {
        self.stmts.iter_mut()
    }

    pub fn get_meta(&self) -> &Meta {
        &self.meta
    }

    pub fn get_mut_meta(&mut self) -> &mut Meta {
        &mut self.meta
    }

    pub fn get_statements(&self) -> &Vec<Statement> {
        &self.stmts
    }

    pub(crate) fn get_statements_mut(&mut self) -> &mut Vec<Statement> {
        &mut self.stmts
    }

    pub fn append_statement(&mut self, stmt: Statement) {
        self.stmts.push(stmt);
    }

    pub(crate) fn get_predecessors_mut(&mut self) -> &mut HashSet<Index> {
        &mut self.predecessors
    }

    pub(crate) fn add_predecessor(&mut self, predecessor: &BasicBlock) {
        debug!(
            "adding predecessor {} to basic block {}",
            predecessor.index, self.index
        );
        self.predecessors.insert(predecessor.index);
    }

    pub(crate) fn get_successors_mut(&mut self) -> &mut HashSet<Index> {
        &mut self.successors
    }

    pub(crate) fn add_successor(&mut self, successor: &BasicBlock) {
        debug!(
            "adding successor {} to basic block {}",
            successor.index, self.index
        );
        self.successors.insert(successor.index);
    }

    pub fn get_variables_read(&self) -> &HashSet<String> {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_read()
    }

    pub fn get_variables_written(&self) -> &HashSet<String> {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_written()
    }
}

impl DirectedGraphNode for BasicBlock {
    fn get_index(&self) -> Index {
        self.index
    }

    fn get_predecessors(&self) -> &HashSet<Index> {
        &self.predecessors
    }

    fn get_successors(&self) -> &HashSet<Index> {
        &self.successors
    }
}

pub fn build_basic_blocks(stmt: &Statement) -> Vec<BasicBlock> {
    let mut basic_blocks = Vec::new();
    visit_statement(stmt, BasicBlock::default(), &mut basic_blocks);
    basic_blocks
}

// Update the CFG with the current statement. This implementation assumes that
// all control-flow statement bodies are wrapped by a `Block` statement. Blocks
// are finalized and the current block is updated when:
//   1. The end of a `Block` statement is reached.
//   2. The current statement is a `While` statement. The current statement is added
//      to the current block, and a new current block is created for the `While`
//      statement body.
//   3. The current statement is an `IfThenElse` statement. The current statement
//      is added to the current block and a new current block is created for the if-
//      case body. If the statement has an else case, a new current block is then
//      created for the else-case body. Finally, a new current block is created when
//      both cases have been visited.
fn visit_statement(
    stmt: &Statement,
    mut current_block: BasicBlock,
    basic_blocks: &mut Vec<BasicBlock>,
) -> BasicBlock {
    use crate::ast::Statement::*;
    let current_index = current_block.get_index();
    assert_eq!(current_index, basic_blocks.len());
    match stmt {
        Block { stmts, .. } => {
            // Add each statement in the basic block to the current block.
            debug!("visiting block statement");
            for stmt in stmts {
                current_block = visit_statement(&stmt, current_block, basic_blocks);
            }
            debug!("leaving block statement");
            let current_index = current_block.get_index();
            assert_eq!(current_index, basic_blocks.len());

            if current_block.len() > 0 {
                debug!("finalizing basic block {current_index}");
                current_block.finalize();
                basic_blocks.push(current_block);
                current_block = BasicBlock::with_predecessor(&mut basic_blocks[current_index]);
            }
            current_block
        }
        While {
            cond,
            stmt: while_body,
            ..
        } => {
            debug!("appending statement 'while {cond}' to basic block {current_index}");
            current_block.append_statement(stmt.clone());

            debug!("finalizing basic block {current_index}");
            current_block.finalize();
            basic_blocks.push(current_block);

            // Visit the while-statement body.
            let while_block = BasicBlock::with_predecessor(&mut basic_blocks[current_index]);
            let mut next_block = visit_statement(&while_body, while_block, basic_blocks);

            // Update and return the next block.
            let current_block = basic_blocks
                .get_mut(current_index)
                .expect("CFG is long enough");
            next_block.add_predecessor(current_block);
            current_block.add_successor(&next_block);
            next_block
        }
        IfThenElse {
            cond,
            if_case,
            else_case,
            ..
        } => {
            debug!("appending statement 'if {cond}' to basic block {current_index}");
            current_block.append_statement(stmt.clone());

            debug!("finalizing basic block {current_index}");
            current_block.finalize();
            basic_blocks.push(current_block);

            // Visit the if-case body.
            debug!("visiting true branch");
            let if_block = BasicBlock::with_predecessor(&mut basic_blocks[current_index]);
            let next_block_if = visit_statement(&if_case, if_block, basic_blocks);

            // Visit the else-case body.
            if let Some(else_case) = else_case {
                debug!("visiting false branch");
                let else_block = BasicBlock::with_predecessor(&mut basic_blocks[current_index]);
                let next_block_else = visit_statement(&else_case, else_block, basic_blocks);

                // Update and return the next block.
                BasicBlock::merge(next_block_if, next_block_else, basic_blocks)
            } else {
                // Return the next block.
                next_block_if
            }
        }
        InitializationBlock {
            initializations, ..
        } => {
            // Add each statement in the initialization block to the current block.
            for stmt in initializations {
                current_block = visit_statement(&stmt, current_block, basic_blocks);
            }
            current_block
        }
        _ => {
            debug!("appending '{stmt}' to basic block {current_index}");
            current_block.append_statement(stmt.clone());
            current_block
        }
    }
}
