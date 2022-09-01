use log::trace;
use std::collections::HashSet;
use std::fmt;

use crate::ir::declarations::Declarations;
use crate::ir::value_meta::ValueEnvironment;
use crate::ssa::traits::DirectedGraphNode;

use crate::ir::variable_meta::{VariableMeta, VariableUses};
use crate::ir::{Meta, Statement};

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
    #[must_use]
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

    #[must_use]
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

    #[must_use]
    pub fn len(&self) -> usize {
        self.stmts.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = &Statement> {
        self.stmts.iter()
    }

    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item = &mut Statement> {
        self.stmts.iter_mut()
    }
    #[must_use]
    pub fn index(&self) -> Index {
        self.index
    }

    #[must_use]
    pub fn meta(&self) -> &Meta {
        &self.meta
    }

    #[must_use]
    pub(crate) fn meta_mut(&mut self) -> &mut Meta {
        &mut self.meta
    }

    #[must_use]
    pub fn statements(&self) -> &Vec<Statement> {
        &self.stmts
    }

    #[must_use]
    pub(crate) fn statements_mut(&mut self) -> &mut Vec<Statement> {
        &mut self.stmts
    }

    pub(crate) fn prepend_statement(&mut self, stmt: Statement) {
        self.stmts.insert(0, stmt);
    }

    pub(crate) fn append_statement(&mut self, stmt: Statement) {
        self.stmts.push(stmt);
    }

    #[must_use]
    pub fn predecessors(&self) -> &IndexSet {
        &self.predecessors
    }

    #[must_use]
    pub fn successors(&self) -> &IndexSet {
        &self.successors
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

    pub fn propagate_values(&mut self, env: &mut ValueEnvironment) -> bool {
        trace!("propagating values for basic block {}", self.index());
        let mut result = false;
        let mut rerun = true;
        while rerun {
            // Rerun value propagation if a single child node was updated.
            rerun = false;
            for stmt in self.iter_mut() {
                rerun = rerun || stmt.propagate_values(env);
            }
            // Return true if a single child node was updated.
            result = result || rerun;
        }
        result
    }

    pub fn propagate_types(&mut self, vars: &Declarations) {
        trace!(
            "propagating variable types for basic block {}",
            self.index()
        );
        for stmt in self.iter_mut() {
            stmt.propagate_types(vars);
        }
    }
}

impl DirectedGraphNode for BasicBlock {
    fn index(&self) -> Index {
        self.index
    }
    fn predecessors(&self) -> &IndexSet {
        &self.predecessors
    }
    fn successors(&self) -> &IndexSet {
        &self.successors
    }
}

impl VariableMeta for BasicBlock {
    fn cache_variable_use(&mut self) {
        trace!("computing variable use for basic block {}", self.index());
        // Variable use for the block is simply the union of the variable use
        // over all statements in the block.
        for stmt in self.iter_mut() {
            stmt.cache_variable_use();
        }

        // Cache variables read.
        let locals_read = self
            .iter()
            .flat_map(|stmt| stmt.locals_read())
            .cloned()
            .collect();

        // Cache variables written.
        let locals_written = self
            .iter()
            .flat_map(|stmt| stmt.locals_written())
            .cloned()
            .collect();

        // Cache signals read.
        let signals_read = self
            .iter()
            .flat_map(|stmt| stmt.signals_read())
            .cloned()
            .collect();

        // Cache signals written.
        let signals_written = self
            .iter()
            .flat_map(|stmt| stmt.signals_written())
            .cloned()
            .collect();

        // Cache components read.
        let components_read = self
            .iter()
            .flat_map(|stmt| stmt.components_read())
            .cloned()
            .collect();

        // Cache components written.
        let components_written = self
            .iter()
            .flat_map(|stmt| stmt.components_written())
            .cloned()
            .collect();

        self.meta_mut()
            .variable_knowledge_mut()
            .set_locals_read(&locals_read)
            .set_locals_written(&locals_written)
            .set_signals_read(&signals_read)
            .set_signals_written(&signals_written)
            .set_components_read(&components_read)
            .set_components_written(&components_written);
    }

    fn locals_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().locals_read()
    }

    fn locals_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().locals_written()
    }

    fn signals_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().signals_read()
    }

    fn signals_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().signals_written()
    }

    fn components_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().components_read()
    }

    fn components_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().components_written()
    }
}

impl fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lines = self
            .iter()
            .map(|stmt| format!("{:?}", stmt))
            .collect::<Vec<_>>();
        let width = lines
            .iter()
            .map(|line| line.len())
            .max()
            .unwrap_or_default();
        let border = format!("+{}+", (0..width + 2).map(|_| '-').collect::<String>());

        writeln!(f, "{}", &border)?;
        for line in lines {
            writeln!(f, "| {:width$} |", line)?;
        }
        writeln!(f, "{}", &border)
    }
}
