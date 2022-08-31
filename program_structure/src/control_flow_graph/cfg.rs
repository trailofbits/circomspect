use log::{debug, trace};
use std::collections::HashSet;
use std::fmt;

use crate::cfg::ssa_impl;
use crate::file_definition::FileID;
use crate::ir::declarations::{Declaration, Declarations};
use crate::ir::value_meta::ValueEnvironment;
use crate::ir::variable_meta::VariableMeta;
use crate::ir::{VariableName, VariableType};
use crate::ssa::dominator_tree::DominatorTree;
use crate::ssa::errors::SSAResult;
use crate::ssa::{insert_phi_statements, insert_ssa_variables};

use super::basic_block::BasicBlock;
use super::parameters::Parameters;
use super::ssa_impl::{Config, Environment};

/// Basic block index type.
pub type Index = usize;

pub struct Cfg {
    name: String,
    parameters: Parameters,
    declarations: Declarations,
    basic_blocks: Vec<BasicBlock>,
    dominator_tree: DominatorTree<BasicBlock>,
}

impl Cfg {
    pub(crate) fn new(
        name: String,
        parameters: Parameters,
        declarations: Declarations,
        basic_blocks: Vec<BasicBlock>,
        dominator_tree: DominatorTree<BasicBlock>,
    ) -> Cfg {
        Cfg {
            name,
            parameters,
            declarations,
            basic_blocks,
            dominator_tree,
        }
    }
    /// Returns the entry (first) block of the CFG.
    #[must_use]
    pub fn entry_block(&self) -> &BasicBlock {
        &self.basic_blocks[Index::default()]
    }

    #[must_use]
    pub fn get_basic_block(&self, index: Index) -> Option<&BasicBlock> {
        self.basic_blocks.get(index)
    }

    /// Returns the number of basic blocks in the CFG.
    #[must_use]
    pub fn len(&self) -> usize {
        self.basic_blocks.len()
    }

    /// Convert the CFG into SSA form.
    pub fn into_ssa(mut self) -> SSAResult<Cfg> {
        debug!("converting `{}` CFG to SSA", self.name());

        // 1. Insert phi statements and convert variables to SSA.
        let mut env = Environment::new(self.parameters(), self.declarations());
        insert_phi_statements::<Config>(&mut self.basic_blocks, &self.dominator_tree, &mut env);
        insert_ssa_variables::<Config>(&mut self.basic_blocks, &self.dominator_tree, &mut env)?;

        // 2. Update parameters to SSA form.
        for name in self.parameters.iter_mut() {
            *name = name.with_version(0);
        }

        // 3. Update declarations to track SSA variables.
        self.declarations =
            ssa_impl::update_declarations(&mut self.basic_blocks, &self.parameters, &env);

        // 4. Propagate metadata to all child nodes. Since determining variable
        // use requires that variable types are available, type propagation must
        // run before caching variable use.
        self.propagate_types();
        self.propagate_values();
        self.cache_variable_use();

        // 5. Print trace output of CFG.
        for basic_block in self.basic_blocks.iter() {
            trace!(
                "basic block {}: (predecessors: {:?}, successors: {:?})",
                basic_block.index(),
                basic_block.predecessors(),
                basic_block.successors(),
            );
            for stmt in basic_block.iter() {
                trace!("    {stmt:?}")
            }
        }
        Ok(self)
    }

    /// Get the name of the corresponding function or template.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the file ID for the corresponding function or template.
    #[must_use]
    pub fn file_id(&self) -> &Option<FileID> {
        &self.parameters.file_id()
    }

    /// Returns the parameter data for the corresponding function or template.
    #[must_use]
    pub fn parameters(&self) -> &Parameters {
        &self.parameters
    }

    /// Returns the variable declaration for the CFG.
    #[must_use]
    pub fn declarations(&self) -> &Declarations {
        &self.declarations
    }

    /// Returns an iterator over the set of variables defined by the CFG.
    pub fn variables(&self) -> impl Iterator<Item = &VariableName> {
        self.declarations.iter().map(|(name, _)| name)
    }

    /// Returns the declaration of the given variable.
    #[must_use]
    pub fn get_declaration(&self, name: &VariableName) -> Option<&Declaration> {
        self.declarations.get_declaration(name)
    }

    /// Returns the type of the given variable.
    #[must_use]
    pub fn get_type(&self, name: &VariableName) -> Option<&VariableType> {
        self.declarations.get_type(name)
    }

    /// Returns an iterator over the basic blocks in the CFG.
    pub fn iter(&self) -> impl Iterator<Item = &BasicBlock> {
        self.basic_blocks.iter()
    }

    /// Returns a mutable iterator over the basic blocks in the CFG.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut BasicBlock> {
        self.basic_blocks.iter_mut()
    }

    /// Returns the dominators of the given basic block
    #[must_use]
    pub fn get_dominators(&self, basic_block: &BasicBlock) -> Vec<&BasicBlock> {
        self.dominator_tree
            .get_dominators(basic_block.index())
            .iter()
            .map(|&i| &self.basic_blocks[i])
            .collect()
    }

    /// Returns the immediate dominator of the basic block (that is, the
    /// predecessor of the node in the CFG dominator tree), if it exists.
    #[must_use]
    pub fn get_immediate_dominator(&self, basic_block: &BasicBlock) -> Option<&BasicBlock> {
        self.dominator_tree
            .get_immediate_dominator(basic_block.index())
            .map(|i| &self.basic_blocks[i])
    }

    /// Get immediate successors of the basic block in the CFG dominator tree.
    /// (For a definition of the dominator relation, see `CFG::get_dominators`.)
    #[must_use]
    pub fn get_dominator_successors(&self, basic_block: &BasicBlock) -> Vec<&BasicBlock> {
        self.dominator_tree
            .get_dominator_successors(basic_block.index())
            .iter()
            .map(|&i| &self.basic_blocks[i])
            .collect()
    }

    /// Returns the dominance frontier of the basic block. The _dominance
    /// frontier_ of `i` is defined as all basic blocks `j` such that `i`
    /// dominates an immediate predecessor of `j`, but i does not strictly
    /// dominate `j`. (`j` is where `i`s dominance ends.)
    #[must_use]
    pub fn get_dominance_frontier(&self, basic_block: &BasicBlock) -> Vec<&BasicBlock> {
        self.dominator_tree
            .get_dominance_frontier(basic_block.index())
            .iter()
            .map(|&i| &self.basic_blocks[i])
            .collect()
    }

    /// Cache variable use for each node in the CFG.
    pub(crate) fn cache_variable_use(&mut self) {
        debug!("computing variable use for `{}`", self.name());
        for basic_block in self.iter_mut() {
            basic_block.cache_variable_use();
        }
    }

    /// Propagate constant values along the CFG.
    pub(crate) fn propagate_values(&mut self) {
        debug!("propagating constant values for `{}`", self.name());
        let mut env = ValueEnvironment::new();
        let mut rerun = true;
        while rerun {
            // Rerun value propagation if a single child node was updated.
            rerun = false;
            for basic_block in self.iter_mut() {
                rerun = rerun || basic_block.propagate_values(&mut env);
            }
        }
    }

    /// Propagate variable types along the CFG.
    pub(crate) fn propagate_types(&mut self) {
        debug!("propagating variable types for `{}`", self.name());
        // Need to clone declarations here since we cannot borrow self both
        // mutably and immutably.
        let declarations = self.declarations.clone();
        for basic_block in self.iter_mut() {
            basic_block.propagate_types(&declarations);
        }
    }
}

impl fmt::Debug for Cfg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for basic_block in self.iter() {
            writeln!(
                f,
                "basic block {}, predecessors: {:?}, successors: {:?}",
                basic_block.index(),
                basic_block.predecessors(),
                basic_block.successors(),
            )?;
            write!(f, "{:?}", basic_block)?;
        }
        Ok(())
    }
}
