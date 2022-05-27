use log::{debug, trace};

use crate::file_definition::FileID;
use crate::ir::declaration_map::{Declaration, DeclarationMap};
use crate::ir::value_meta::ValueEnvironment;
use crate::ir::variable_meta::VariableMeta;
use crate::ir::VariableName;
use crate::ssa::dominator_tree::DominatorTree;
use crate::ssa::errors::SSAResult;
use crate::ssa::traits::Version;
use crate::ssa::{insert_phi_statements, insert_ssa_variables};

use super::basic_block::BasicBlock;
use super::param_data::ParameterData;
use super::ssa_impl::VersionEnvironment;

/// Basic block index type.
pub type Index = usize;

pub struct Cfg {
    name: String,
    parameters: ParameterData,
    declarations: DeclarationMap,
    basic_blocks: Vec<BasicBlock>,
    dominator_tree: DominatorTree<BasicBlock>,
}

impl Cfg {
    pub(crate) fn new(
        name: String,
        parameters: ParameterData,
        declarations: DeclarationMap,
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
    pub fn get_entry_block(&self) -> &BasicBlock {
        &self.basic_blocks[Index::default()]
    }

    #[must_use]
    pub fn get_basic_block(&self, index: Index) -> Option<&BasicBlock> {
        self.basic_blocks.get(index)
    }

    /// Returns the number of basic blocks in the CFG.
    #[must_use]
    pub fn nof_basic_blocks(&self) -> usize {
        self.basic_blocks.len()
    }
    /// Convert the CFG into SSA form.
    pub fn into_ssa(&mut self) -> SSAResult<()> {
        debug!("converting `{}` CFG to SSA", self.get_name());

        // 1. Cache variable use before running SSA.
        self.cache_variable_use();

        // 2. Insert phi statements and convert variables to SSA.
        let mut env = VersionEnvironment::new(self.get_parameters(), self.get_declarations());
        insert_phi_statements(&mut self.basic_blocks, &self.dominator_tree);
        insert_ssa_variables(&mut self.basic_blocks, &self.dominator_tree, &mut env)?;

        // 3. Update parameters to SSA form.
        for name in self.parameters.iter_mut() {
            *name = name.with_version(Version::default());
        }

        // 4. Re-cache variable use, and run value propagation.
        self.cache_variable_use();
        self.propagate_values();

        // 5. Update declaration map to track SSA variables.
        let mut versioned_declarations = DeclarationMap::new();
        for (name, declaration) in self.declarations.iter() {
            for version in env
                .get_version_range(name)
                .expect("variable in environment")
            {
                let versioned_name = declaration.get_name().with_version(version);
                let versioned_declaration = Declaration::new(
                    &versioned_name,
                    declaration.get_type(),
                    declaration.get_dimensions(),
                    declaration.get_file_id(),
                    &declaration.get_location(),
                );
                versioned_declarations.add_declaration(&versioned_name, versioned_declaration);
            }
        }
        self.declarations = versioned_declarations;

        for basic_block in self.basic_blocks.iter() {
            trace!(
                "basic block {}: (predecessors: {:?}, successors: {:?})",
                basic_block.get_index(),
                basic_block.get_predecessors(),
                basic_block.get_successors(),
            );
            for stmt in basic_block.iter() {
                trace!("    `{stmt};`")
            }
        }
        Ok(())
    }

    /// Get the name of the corresponding function or template.
    #[must_use]
    pub fn get_name(&self) -> &str {
        &self.name
    }

    /// Get the file ID for the corresponding function or template.
    #[must_use]
    pub fn get_file_id(&self) -> &Option<FileID> {
        &self.parameters.get_file_id()
    }

    /// Returns the parameter data for the corresponding function or template.
    #[must_use]
    pub fn get_parameters(&self) -> &ParameterData {
        &self.parameters
    }

    #[must_use]
    pub fn get_declarations(&self) -> &DeclarationMap {
        &self.declarations
    }

    #[must_use]
    pub fn get_variables(&self) -> impl Iterator<Item = &VariableName> {
        self.declarations.iter().map(|(name, _)| name)
    }

    pub fn get_declaration(&self, name: &VariableName) -> Option<&Declaration> {
        self.declarations.get_declaration(name)
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
            .get_dominators(basic_block.get_index())
            .iter()
            .map(|&i| &self.basic_blocks[i])
            .collect()
    }

    /// Returns the immediate dominator of the basic block (that is, the
    /// predecessor of the node in the CFG dominator tree), if it exists.
    #[must_use]
    pub fn get_immediate_dominator(&self, basic_block: &BasicBlock) -> Option<&BasicBlock> {
        self.dominator_tree
            .get_immediate_dominator(basic_block.get_index())
            .map(|i| &self.basic_blocks[i])
    }

    /// Get immediate successors of the basic block in the CFG dominator tree.
    /// (For a definition of the dominator relation, see `CFG::get_dominators`.)
    #[must_use]
    pub fn get_dominator_successors(&self, basic_block: &BasicBlock) -> Vec<&BasicBlock> {
        self.dominator_tree
            .get_dominator_successors(basic_block.get_index())
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
            .get_dominance_frontier(basic_block.get_index())
            .iter()
            .map(|&i| &self.basic_blocks[i])
            .collect()
    }

    /// Cache variable use for each node in the CFG.
    fn cache_variable_use(&mut self) {
        debug!("computing variable use for `{}`", self.get_name());
        for basic_block in self.iter_mut() {
            basic_block.cache_variable_use();
        }
    }

    /// Propagate constant values along the CFG.
    fn propagate_values(&mut self) {
        debug!("propagating constant values for `{}`", self.get_name());
        let mut env = ValueEnvironment::new();
        while self
            .iter_mut()
            .any(|basic_block| basic_block.propagate_values(&mut env))
        {}
    }
}
