use log::trace;
use std::collections::HashSet;

use crate::static_single_assignment::traits::DirectedGraphNode;

use crate::ir::ir::{Meta, Statement};
use crate::ir::variable_meta::{VariableMeta, VariableSet};

type Index = usize;
type IndexSet = HashSet<Index>;

#[derive(Clone)]
pub struct BasicBlock {
    index: Index,
    meta: Meta,
    stmts: Vec<Statement>,
    predecessors: IndexSet,
    successors: IndexSet,
}

impl BasicBlock {
    pub fn new(index: Index, meta: Meta) -> BasicBlock {
        trace!("creating basic block {index}");
        BasicBlock {
            meta,
            index,
            stmts: Vec::new(),
            predecessors: IndexSet::new(),
            successors: IndexSet::new(),
        }
    }

    pub fn from_raw_parts(
        index: Index,
        meta: Meta,
        stmts: Vec<Statement>,
        predecessors: IndexSet,
        successors: IndexSet,
    ) -> BasicBlock {
        BasicBlock {
            index,
            meta,
            stmts,
            predecessors,
            successors,
        }
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
    pub fn get_meta_mut(&mut self) -> &mut Meta {
        &mut self.meta
    }
    pub fn get_statements(&self) -> &Vec<Statement> {
        &self.stmts
    }
    pub fn get_statements_mut(&mut self) -> &mut Vec<Statement> {
        &mut self.stmts
    }
    pub(crate) fn prepend_statement(&mut self, stmt: Statement) {
        self.stmts.insert(0, stmt);
    }
    pub(crate) fn append_statement(&mut self, stmt: Statement) {
        self.stmts.push(stmt);
    }
    pub(crate) fn add_predecessor(&mut self, predecessor: Index) {
        trace!(
            "adding predecessor {} to basic block {}",
            predecessor,
            self.index
        );
        self.predecessors.insert(predecessor);
    }
    pub(crate) fn add_successor(&mut self, successor: Index) {
        trace!(
            "adding successor {} to basic block {}",
            successor,
            self.index
        );
        self.successors.insert(successor);
    }
}

impl DirectedGraphNode for BasicBlock {
    fn get_index(&self) -> Index {
        self.index
    }
    fn get_predecessors(&self) -> &IndexSet {
        &self.predecessors
    }
    fn get_successors(&self) -> &IndexSet {
        &self.successors
    }
}

impl VariableMeta for BasicBlock {
    fn cache_variable_use(&mut self) {
        trace!(
            "(re)computing variable use for basic block {}",
            self.get_index()
        );
        // Cache variable use for each individual statement.
        self.iter_mut().for_each(|stmt| stmt.cache_variable_use());
        // Variable use for the block is simply the union of the variable use
        // over all statements in the block.
        let mut variables_read = VariableSet::new();
        self.iter()
            .map(|stmt| stmt.get_variables_written())
            .for_each(|update| variables_read.extend(update.iter().cloned()));
        self.get_meta_mut()
            .get_mut_variable_knowledge()
            .set_variables_read(&variables_read);
        let mut variables_written = VariableSet::new();
        self.iter()
            .map(|stmt| stmt.get_variables_written())
            .for_each(|update| variables_written.extend(update.iter().cloned()));
        self.get_meta_mut()
            .get_mut_variable_knowledge()
            .set_variables_written(&variables_written);
    }

    fn get_variables_read(&self) -> &VariableSet {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_read()
    }
    fn get_variables_written(&self) -> &VariableSet {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_written()
    }
}
