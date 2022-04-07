use log::debug;
use std::collections::HashSet;

use super::basic_block::{build_basic_blocks, BasicBlock};
use super::dominator_tree::DominatorTree;
use super::ssa::{insert_phi_statements, insert_ssa_variables};

use crate::function_data::FunctionData;
use crate::template_data::TemplateData;
use crate::utils::directed_graph::DirectedGraphNode;

type Index = usize;

pub struct CFG {
    parameters: Vec<String>,
    basic_blocks: Vec<BasicBlock>,
    dominator_tree: DominatorTree<BasicBlock>,
}

impl CFG {
    pub fn from_template(template: &TemplateData) -> CFG {
        let parameters = template.get_name_of_params().clone();
        let basic_blocks = build_basic_blocks(template.get_body());
        let dominator_tree = DominatorTree::new(&basic_blocks);
        for basic_block in &basic_blocks {
            debug!("basic block {} is given by:", basic_block.get_index());
            for stmt in basic_block.iter() {
                debug!("    {}", stmt);
            }
            debug!("    variables read: {:?}", basic_block.get_variables_read());
            debug!(
                "    variables written: {:?}",
                basic_block.get_variables_written()
            );
        }
        CFG {
            parameters,
            basic_blocks,
            dominator_tree,
        }
    }

    pub fn from_function(function: &FunctionData) -> CFG {
        let parameters = function.get_name_of_params().clone();
        let basic_blocks = build_basic_blocks(function.get_body());
        let dominator_tree = DominatorTree::new(&basic_blocks);
        CFG {
            parameters,
            basic_blocks,
            dominator_tree,
        }
    }

    pub fn get_entry_block(&self) -> &BasicBlock {
        &self.basic_blocks[Index::default()]
    }

    pub fn nof_basic_blocks(&self) -> usize {
        self.basic_blocks.len()
    }

    pub fn into_ssa(&mut self) -> &mut CFG {
        // TODO: We *must* replace any shadowing variables first.
        insert_phi_statements(&mut self.basic_blocks, &self.dominator_tree);
        insert_ssa_variables(&mut self.basic_blocks, &self.dominator_tree);
        self
    }

    pub fn iter(&self) -> impl Iterator<Item = &BasicBlock> {
        self.basic_blocks.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut BasicBlock> {
        self.basic_blocks.iter_mut()
    }

    pub fn get_basic_block(&self, i: usize) -> &BasicBlock {
        &self.basic_blocks[i]
    }

    pub fn get_basic_block_mut(&mut self, i: usize) -> &mut BasicBlock {
        &mut self.basic_blocks[i]
    }

    pub fn update_basic_block<F: Fn(&mut BasicBlock)>(
        &mut self,
        basic_block: &BasicBlock,
        update: F,
    ) {
        update(&mut self.basic_blocks[basic_block.get_index()]);
    }

    pub fn get_dominator_tree(&self) -> &DominatorTree<BasicBlock> {
        &self.dominator_tree
    }

    pub fn get_dominators(&self, basic_block: &BasicBlock) -> HashSet<usize> {
        self.get_dominator_tree()
            .get_dominators(basic_block.get_index())
    }

    pub fn get_immediate_dominator(&self, basic_block: &BasicBlock) -> Option<usize> {
        self.dominator_tree
            .get_immediate_dominator(basic_block.get_index())
    }

    // Get immediate successors in the CFG dominator tree.
    pub fn get_dominator_successors(&self, basic_block: &BasicBlock) -> HashSet<usize> {
        self.dominator_tree
            .get_dominator_successors(basic_block.get_index())
    }

    // The dominance frontier of i is defined as all basic blocks j such that i dominates an
    // immediate predecessor of j, but i does not strictly dominate j. (j is where i's dominance
    // ends.)
    pub fn get_dominance_frontier(&self, basic_block: &BasicBlock) -> HashSet<usize> {
        self.dominator_tree
            .get_dominance_frontier(basic_block.get_index())
    }
}
