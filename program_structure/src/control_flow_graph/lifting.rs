use log::{debug, trace};
use std::collections::HashSet;

use crate::ast;
use crate::ast::Definition;

use crate::function_data::FunctionData;
use crate::ir;
use crate::ir::declarations::{Declaration, Declarations};
use crate::ir::errors::IRResult;
use crate::ir::lifting::{LiftingEnvironment, TryLift};
use crate::ir::VariableType;

use crate::error_definition::ReportCollection;
use crate::nonempty_vec::NonEmptyVec;
use crate::ssa::dominator_tree::DominatorTree;
use crate::template_data::TemplateData;

use super::basic_block::BasicBlock;
use super::cfg::DefinitionType;
use super::errors::{CFGError, CFGResult};
use super::parameters::Parameters;
use super::unique_vars::ensure_unique_variables;
use super::Cfg;

type Index = usize;
type IndexSet = HashSet<Index>;
type BasicBlockVec = NonEmptyVec<BasicBlock>;

/// This is a high level trait which simply wraps the implementation provided by `TryLift`.
pub trait IntoCfg {
    fn into_cfg(&self, reports: &mut ReportCollection) -> CFGResult<Cfg>;
}

impl<T> IntoCfg for T
where
    T: TryLift<(), IR = Cfg, Error = CFGError>,
{
    fn into_cfg(&self, reports: &mut ReportCollection) -> CFGResult<Cfg> {
        self.try_lift((), reports)
    }
}

impl From<&Parameters> for LiftingEnvironment {
    fn from(params: &Parameters) -> LiftingEnvironment {
        let mut env = LiftingEnvironment::new();
        for name in params.iter() {
            let declaration = Declaration::new(
                name,
                &VariableType::Local,
                params.file_id(),
                params.file_location(),
            );
            env.add_declaration(&declaration);
        }
        env
    }
}

impl TryLift<()> for &TemplateData {
    type IR = Cfg;
    type Error = CFGError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> CFGResult<Cfg> {
        let name = self.get_name().to_string();
        let parameters = Parameters::from(*self);
        let body = self.get_body().clone();

        debug!("building CFG for template `{name}`");
        try_lift_impl(name, DefinitionType::Template, parameters, body, reports)
    }
}

impl TryLift<()> for &FunctionData {
    type IR = Cfg;
    type Error = CFGError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> CFGResult<Cfg> {
        let name = self.get_name().to_string();
        let parameters = Parameters::from(*self);
        let body = self.get_body().clone();

        debug!("building CFG for function `{name}`");
        try_lift_impl(name, DefinitionType::Function, parameters, body, reports)
    }
}

impl TryLift<()> for Definition {
    type IR = Cfg;
    type Error = CFGError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> CFGResult<Cfg> {
        match self {
            Definition::Template { name, body, .. } => {
                debug!("building CFG for template `{name}`");
                try_lift_impl(name.clone(), DefinitionType::Template, self.into(), body.clone(), reports)
            }
            Definition::Function { name, body, .. } => {
                debug!("building CFG for function `{name}`");
                try_lift_impl(name.clone(), DefinitionType::Function, self.into(), body.clone(), reports)
            }
        }
    }
}

fn try_lift_impl(
    name: String,
    definition_type: DefinitionType,
    parameters: Parameters,
    mut body: ast::Statement,
    reports: &mut ReportCollection,
) -> CFGResult<Cfg> {
    // 1. Ensure that variable names are globally unique before converting to basic blocks.
    ensure_unique_variables(&mut body, &parameters, reports)?;

    // 2. Convert template AST to CFG and compute dominator tree.
    let mut env = LiftingEnvironment::from(&parameters);
    let basic_blocks = build_basic_blocks(&body, &mut env, reports)?;
    let dominator_tree = DominatorTree::new(&basic_blocks);
    let declarations = Declarations::from(env);
    let mut cfg = Cfg::new(name, definition_type, parameters, declarations, basic_blocks, dominator_tree);

    // 3. Propagate metadata to all child nodes. Since determining variable use
    // requires that variable types are available, type propagation must run
    // before caching variable use.
    //
    // Note that the current implementation of value propagation only makes
    // sense in SSA form.
    cfg.propagate_types();
    cfg.cache_variable_use();

    Ok(cfg)
}

/// This function generates a vector of basic blocks containing `ir::Statement`s
/// from a function or template body. The vector is guaranteed to be non-empty,
/// and the first block (with index 0) will always be the entry block.
pub(crate) fn build_basic_blocks(
    body: &ast::Statement,
    env: &mut LiftingEnvironment,
    reports: &mut ReportCollection,
) -> IRResult<Vec<BasicBlock>> {
    assert!(matches!(body, ast::Statement::Block { .. }));

    let meta = body.get_meta().try_lift((), reports)?;
    let mut basic_blocks = BasicBlockVec::new(BasicBlock::new(Index::default(), meta));
    visit_statement(body, env, reports, &mut basic_blocks)?;
    Ok(basic_blocks.into())
}

/// Update the CFG with the current statement. This implementation assumes that
/// all control-flow statement bodies are wrapped by a `Block` statement. Blocks
/// are finalized and the current block (i.e. last block) is updated when:
///
///   2. The current statement is a `While` statement. An `IfThenElse` statement
///      is added to the current block. The successors of the if-statement will be
///      the while-statement body and the while-statement successor (if any).
///   3. The current statement is an `IfThenElse` statement. The current statement
///      is added to the current block. The successors of the if-statement will
///      be the if-case body and else-case body (if any).
///
/// The function returns the predecessors of the next block in the CFG.
fn visit_statement(
    stmt: &ast::Statement,
    env: &mut LiftingEnvironment,
    reports: &mut ReportCollection,
    basic_blocks: &mut BasicBlockVec,
) -> IRResult<IndexSet> {
    let current_index = basic_blocks.last().index();

    match stmt {
        ast::Statement::InitializationBlock {
            initializations: stmts,
            ..
        } => {
            // Add each statement in the initialization block to the current
            // block. Since initialization blocks only contain declarations and
            // substitutions, we do not need to track predecessors here.
            trace!("entering initialization block statement");
            for stmt in stmts {
                assert!(visit_statement(stmt, env, reports, basic_blocks)?.is_empty());
            }
            trace!("leaving initialization block statement");
            Ok(HashSet::new())
        }
        ast::Statement::Block { stmts, .. } => {
            // Add each statement in the basic block to the current block. If a
            // call to `visit_statement` completes a basic block and returns a set
            // of predecessors for the next block, we create a new block before
            // continuing.
            trace!("entering block statement");

            let mut pred_set = IndexSet::new();
            for stmt in stmts {
                if !pred_set.is_empty() {
                    let meta = stmt.get_meta().try_lift((), reports)?;
                    complete_basic_block(basic_blocks, &pred_set, meta);
                }
                pred_set = visit_statement(stmt, env, reports, basic_blocks)?;
            }
            trace!("leaving block statement (predecessors: {:?})", pred_set);

            // If the last statement of the block is a control-flow statement,
            // `pred_set` will be non-empty. Otherwise it will be empty.
            Ok(pred_set)
        }
        ast::Statement::While {
            meta,
            cond,
            stmt: while_body,
            ..
        } => {
            let pred_set = HashSet::from([current_index]);
            complete_basic_block(basic_blocks, &pred_set, meta.try_lift((), reports)?);

            // While statements are translated into a loop head with a single
            // if-statement, and a loop body containing the while-statement
            // body. The index of the loop header will be `current_index + 1`,
            // and the index of the loop body will be `current_index + 2`.
            trace!("appending statement `if {cond}` to basic block {current_index}");
            basic_blocks
                .last_mut()
                .append_statement(ir::Statement::IfThenElse {
                    meta: meta.try_lift((), reports)?,
                    cond: cond.try_lift((), reports)?,
                    true_index: current_index + 2,
                    false_index: None, // May be updated later.
                });
            let header_index = current_index + 1;

            // Visit the while-statement body.
            let meta = while_body.get_meta().try_lift((), reports)?;
            let pred_set = HashSet::from([header_index]);
            complete_basic_block(basic_blocks, &pred_set, meta);

            trace!("visiting while body");
            let mut pred_set = visit_statement(while_body, env, reports, basic_blocks)?;
            // The returned predecessor set will be empty if the last statement
            // of the body is not a conditional. In this case we need to add the
            // last block of the body to complete the corresponding block.
            if pred_set.is_empty() {
                pred_set.insert(basic_blocks.last().index());
            }
            // The loop header is the successor of all blocks in `pred_set`.
            trace!(
                "adding predecessors {:?} to loop header {header_index}",
                pred_set
            );
            for i in pred_set {
                basic_blocks[i].add_successor(header_index);
                basic_blocks[header_index].add_predecessor(i);
            }

            // The next block (if any) will be the false branch and a successor
            // of the loop header.
            Ok(HashSet::from([header_index]))
        }
        ast::Statement::IfThenElse {
            meta,
            cond,
            if_case,
            else_case,
            ..
        } => {
            trace!("appending statement `if {cond}` to basic block {current_index}");
            basic_blocks
                .last_mut()
                .append_statement(ir::Statement::IfThenElse {
                    meta: meta.try_lift((), reports)?,
                    cond: cond.try_lift((), reports)?,
                    true_index: current_index + 1,
                    false_index: None, // May be updated later.
                });

            // Visit the if-case body.
            let meta = if_case.get_meta().try_lift((), reports)?;
            let pred_set = HashSet::from([current_index]);
            complete_basic_block(basic_blocks, &pred_set, meta);

            trace!("visiting true if-statement branch");
            let mut if_pred_set = visit_statement(if_case, env, reports, basic_blocks)?;
            // The returned predecessor set will be empty if the last statement
            // of the body is not a conditional. In this case we need to add the
            // last block of the body to complete the corresponding block.
            if if_pred_set.is_empty() {
                if_pred_set.insert(basic_blocks.last().index());
            }

            // Visit the else-case body.
            if let Some(else_case) = else_case {
                trace!("visiting false if-statement branch");
                let meta = else_case.get_meta().try_lift((), reports)?;
                let pred_set = HashSet::from([current_index]);
                complete_basic_block(basic_blocks, &pred_set, meta);

                let mut else_pred_set = visit_statement(else_case, env, reports, basic_blocks)?;
                // The returned predecessor set will be empty if the last statement
                // of the body is not a conditional. In this case we need to add the
                // last block of the body to complete the corresponding block.
                if else_pred_set.is_empty() {
                    else_pred_set.insert(basic_blocks.last().index());
                }
                Ok(if_pred_set.union(&else_pred_set).cloned().collect())
            } else {
                if_pred_set.insert(current_index);
                Ok(if_pred_set)
            }
        }
        ast::Statement::Declaration {
            meta, name, xtype, ..
        } => {
            // Declarations are also tracked by the CFG header.
            trace!("appending `{stmt}` to basic block {current_index}");
            env.add_declaration(&Declaration::new(
                &name.try_lift(meta, reports)?,
                &xtype.try_lift((), reports)?,
                &meta.file_id,
                &meta.location,
            ));
            basic_blocks
                .last_mut()
                .append_statement(stmt.try_lift((), reports)?);
            Ok(HashSet::new())
        }
        _ => {
            trace!("appending `{stmt}` to basic block {current_index}");
            basic_blocks
                .last_mut()
                .append_statement(stmt.try_lift((), reports)?);
            Ok(HashSet::new())
        }
    }
}

/// Complete the current (i.e. last) basic block and add a new basic block to
/// the vector with the given `meta`, and `pred_set` as predecessors. Update all
/// predecessors adding the new block as a successor.
///
/// If the final statement of the predecessor block is a control-flow statement,
/// and the new block is not the true branch target of the statement, the new
/// block is added as the false branch target.
fn complete_basic_block(basic_blocks: &mut BasicBlockVec, pred_set: &IndexSet, meta: ir::Meta) {
    use ir::Statement::*;
    trace!("finalizing basic block {}", basic_blocks.last().index());
    let j = basic_blocks.len();
    basic_blocks.push(BasicBlock::new(j, meta));
    for i in pred_set {
        basic_blocks[i].add_successor(j);
        basic_blocks[j].add_predecessor(*i);

        // If the final statement `S` of block `i` is a control flow statement,
        // and `j` is not the true branch of `S`, update the false branch of `S`
        // to `j`.
        if let Some(IfThenElse {
            cond,
            true_index,
            false_index,
            ..
        }) = basic_blocks[i].statements_mut().last_mut()
        {
            if j != *true_index && false_index.is_none() {
                trace!("updating false branch target of `if {cond}`");
                *false_index = Some(j)
            }
        }
    }
}
