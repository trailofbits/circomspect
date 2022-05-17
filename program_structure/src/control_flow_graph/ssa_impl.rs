use log::trace;
use std::collections::{HashMap, HashSet};

use crate::ir::ir::*;
use crate::ir::variable_meta::VariableMeta;
use crate::ssa::errors::{SSAError, SSAResult};
use crate::ssa::traits::{SSABasicBlock, SSAEnvironment, SSAStatement, VariableSet};

use super::basic_block::BasicBlock;
use super::param_data::ParameterData;

type Version = usize;

#[derive(Clone)]
pub struct VersionEnvironment {
    variables: HashMap<String, Version>,
    signals: HashSet<String>,
    components: HashSet<String>,
}

impl VersionEnvironment {
    pub fn new() -> VersionEnvironment {
        VersionEnvironment {
            variables: HashMap::new(),
            signals: HashSet::new(),
            components: HashSet::new(),
        }
    }
}

impl From<&ParameterData> for VersionEnvironment {
    fn from(params: &ParameterData) -> VersionEnvironment {
        let mut env = VersionEnvironment::new();
        for name in params.iter() {
            env.add_variable(&name.to_string(), Version::default())
        }
        env
    }
}

impl SSAEnvironment for VersionEnvironment {
    fn add_variable(&mut self, name: &str, version: Version) {
        trace!("adding {name} version from environment: {version:?}");
        self.variables.insert(name.to_string(), version);
    }

    fn add_signal(&mut self, name: &str) {
        self.signals.insert(name.to_string());
    }

    fn add_component(&mut self, name: &str) {
        self.components.insert(name.to_string());
    }

    fn has_variable(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }

    fn has_signal(&self, name: &str) -> bool {
        self.signals.contains(name)
    }

    fn has_component(&self, name: &str) -> bool {
        self.signals.contains(name)
    }

    fn get_variable(&self, name: &str) -> Option<Version> {
        trace!(
            "getting {name} version from environment: {:?}",
            self.variables.get(name)
        );
        self.variables.get(name).cloned()
    }
}

impl SSABasicBlock for BasicBlock {
    type Statement = Statement;

    fn insert_statement(&mut self, stmt: Self::Statement) {
        self.prepend_statement(stmt);
    }

    fn get_statements<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Statement> + 'a> {
        Box::new(self.iter())
    }

    fn get_statements_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Statement> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl SSAStatement for Statement {
    fn get_variables_written(&self) -> VariableSet {
        VariableMeta::get_variables_written(self).clone()
    }

    fn new_phi_statement(name: &str) -> Self {
        use AssignOp::*;
        use Expression::*;
        use Statement::*;
        let phi = Phi {
            meta: Meta::new(0, 0),
            // φ expression arguments are added later.
            args: Vec::new(),
        };
        let mut stmt = Substitution {
            meta: Meta::new(0, 0),
            // Variable name is versioned lated.
            var: VariableName::name(name),
            op: AssignVar,
            rhe: phi,
            access: Vec::new(),
        };
        stmt.cache_variable_use();
        stmt
    }

    fn is_phi_statement(&self) -> bool {
        use Expression::*;
        use Statement::*;
        match self {
            Substitution {
                rhe: Phi { .. }, ..
            } => true,
            _ => false,
        }
    }

    fn is_phi_statement_for(&self, name: &str) -> bool {
        use Expression::*;
        use Statement::*;
        match self {
            Substitution {
                var,
                rhe: Phi { .. },
                ..
            } => var.to_string() == name,
            _ => false,
        }
    }

    fn ensure_phi_argument(&mut self, env: &impl SSAEnvironment) {
        use Expression::*;
        use Statement::*;
        match self {
            // If this is a φ statement we ensure that the RHS contains the
            // variable version from the given SSA environment.
            Substitution {
                var: name,
                rhe: Phi { args, .. },
                ..
            } => {
                let unversioned_name = name.without_version();
                trace!("φ statement for variable '{name}' found");
                if let Some(env_version) = env.get_variable(&unversioned_name.to_string()) {
                    // If the argument list does not contain the SSA variable we add it.
                    if args.iter().any(|arg| {
                        matches!(
                            arg,
                            Variable { version: arg_version, ..  } if *arg_version == Some(env_version)
                        )
                    }) {
                        return;
                    }
                    args.push(Variable {
                        meta: Meta::new(0, 0),
                        name: unversioned_name,
                        access: Vec::new(),
                        version: Some(env_version),
                    });
                    self.cache_variable_use();
                }
            }
            // If this is not a φ statement we panic.
            _ => panic!("expected φ statement"),
        }
    }

    fn insert_ssa_variables(&mut self, env: &mut impl SSAEnvironment) -> SSAResult<()> {
        trace!("converting '{self}' to SSA");
        use Statement::*;
        let result = match self {
            IfThenElse { cond, .. } => visit_expression(cond, env),
            Return { value, .. } => visit_expression(value, env),
            Declaration { xtype, name, .. } => {
                assert!(name.get_version().is_none());
                use VariableType::*;
                *name = match xtype {
                    Var => {
                        // A declaration is always the first occurrence of the variable.
                        // The variable is only added to the environment on first use.
                        let versioned_name = name.with_version(Version::default());

                        trace!(
                            "replacing (declared) variable '{name}' with SSA variable '{versioned_name}'"
                        );
                        versioned_name
                    }
                    Component => {
                        // Component names are not versioned.
                        env.add_component(&name.to_string());
                        name.clone()
                    }
                    Signal(_, _) => {
                        // Signal names are not versioned.
                        env.add_signal(&name.to_string());
                        name.clone()
                    }
                };
                Ok(())
            }
            Substitution { var, op, rhe, .. } => {
                assert!(var.get_version().is_none());
                // We need to visit the right-hand expression before updating the environment.
                visit_expression(rhe, env)?;
                *var = match op {
                    // If this is a variable assignment we need to version the variable.
                    AssignOp::AssignVar => {
                        // If this is the first assignment to the variable we set the version to 0.
                        let version = env
                            .get_variable(&var.to_string_without_version())
                            .map(|version| version + 1)
                            .unwrap_or_default();
                        env.add_variable(&var.to_string(), version);
                        let versioned_var = var.with_version(version);

                        trace!(
                            "replacing (written) variable '{var}' with SSA variable '{versioned_var}'"
                        );
                        versioned_var
                    }
                    // If this is a signal or component assignment we ignore it.
                    _ => var.clone(),
                };
                Ok(())
            }
            ConstraintEquality { lhe, rhe, .. } => {
                visit_expression(lhe, env)?;
                visit_expression(rhe, env)
            }
            LogCall { arg, .. } => visit_expression(arg, env),
            Assert { arg, .. } => visit_expression(arg, env),
        };
        // Since variables names may have changed we need to re-cache variable use.
        self.cache_variable_use();
        result
    }
}

/// Replaces each occurrence of the variable `v` with a versioned SSA variable `v.n`.
/// Currently, signals and components are not touched.
fn visit_expression(expr: &mut Expression, env: &impl SSAEnvironment) -> SSAResult<()> {
    use Expression::*;
    match expr {
        // Variables are decorated with the corresponding SSA version.
        Variable {
            meta,
            name,
            version: var_version,
            ..
        } => {
            assert!(
                var_version.is_none(),
                "variable already converted to SSA form"
            );
            match env.get_variable(&name.to_string_without_version()) {
                Some(env_version) => {
                    *var_version = Some(env_version);
                    trace!("replacing (read) variable '{name}' with SSA variable '{name}.{env_version}'");
                    Ok(())
                }
                None => {
                    trace!("failed to convert undeclared variable '{name}' to SSA");
                    Err(SSAError::UndefinedVariableError {
                        name: name.to_string(),
                        file_id: meta.get_file_id(),
                        location: meta.file_location(),
                    })
                }
            }
        }
        // For all other expression types we simply recurse into their children.
        PrefixOp { rhe, .. } => visit_expression(rhe, env),
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, env)?;
            visit_expression(rhe, env)
        }
        InlineSwitchOp {
            cond,
            if_true,
            if_false,
            ..
        } => {
            visit_expression(cond, env)?;
            visit_expression(if_true, env)?;
            visit_expression(if_false, env)
        }
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, env)?;
            }
            Ok(())
        }
        ArrayInLine { values, .. } => {
            for value in values {
                visit_expression(value, env)?;
            }
            Ok(())
        }
        // φ expression arguments are updated in a later pass.
        Phi { .. } | Signal { .. } | Component { .. } | Number(_, _) => Ok(()),
    }
}

// // Returns the name (as a `String`) of the SSA variable with the given version.
// fn get_ssa_variable_name(name: &str, version: usize) -> String {
//     use Expression::*;
//     let var = Variable {
//         meta: Meta::new(0, 0),
//         name: name.to_string(),
//         access: Vec::new(),
//         version: Some(version),
//     };
//     format!("{}", var)
// }
// /// Insert a dummy φ statement in block `j`, for each variable written in block
// /// `i`, if `j` is in the dominance frontier of `i`. The variables are still not
// /// in SSA form.
// pub fn insert_phi_statements(
//     basic_blocks: &mut Vec<BasicBlock>,
//     dominator_tree: &DominatorTree<BasicBlock>,
// ) {
//     // Insert φ statements at the dominance frontier of each block.
//     let mut work_list: Vec<Index> = (0..basic_blocks.len()).collect();
//     while let Some(current_index) = work_list.pop() {
//         let variables_written = {
//             let current_block = &basic_blocks[current_index];
//             current_block.get_variables_written().clone()
//         };
//         if variables_written.is_empty() {
//             trace!("basic block {current_index} does not write any variables");
//             continue;
//         }
//         trace!(
//             "dominance frontier for block {current_index} is {:?}",
//             dominator_tree.get_dominance_frontier(current_index)
//         );
//         for frontier_index in dominator_tree.get_dominance_frontier(current_index) {
//             let mut frontier_block = &mut basic_blocks[frontier_index];
//             for name in &variables_written {
//                 if ensure_phi_statement(&mut frontier_block, &name) {
//                     // If a phi statement was added to the block we need to re-add the frontier
//                     // block to the work list.
//                     work_list.push(frontier_index);
//                 }
//             }
//         }
//     }
// }
//
// fn ensure_phi_statement(basic_block: &mut BasicBlock, name: &String) -> bool {
//     if !has_phi_statement(basic_block, name) {
//         trace!(
//             "inserting new φ statement for variable '{name}' in block {}",
//             basic_block.get_index()
//         );
//         let stmt = build_phi_statement(name);
//         basic_block.prepend_statement(stmt);
//         basic_block.cache_variable_use(); // Update variable use.
//         return true;
//     }
//     false
// }
//
// fn has_phi_statement(basic_block: &BasicBlock, name: &String) -> bool {
//     use Expression::Phi;
//     use Statement::Substitution;
//     basic_block.iter().any(|stmt| match stmt {
//         Substitution {
//             var,
//             rhe: Phi { .. },
//             ..
//         } => var == name,
//         _ => false,
//     })
// }
//
// fn build_phi_statement(name: &String) -> Statement {
//     use AssignOp::*;
//     use Expression::*;
//     use Statement::*;
//     let phi = Phi {
//         meta: Meta::new(0, 0),
//         // φ expression arguments are added later.
//         args: Vec::new(),
//     };
//     Substitution {
//         meta: Meta::new(0, 0),
//         var: name.clone(),
//         op: AssignVar,
//         rhe: phi,
//         access: Vec::new(),
//     }
// }
//
// // Update the RHS of each φ statement in the basic block with the SSA variable
// // versions from the given environment. The LHS will be updated when this basic
// // block is reached in the dominance tree.
// fn update_phi_statements(basic_block: &mut BasicBlock, env: &SSAEnvironment) {
//     use Expression::{Phi, Variable};
//     use Statement::Substitution;
//     trace!(
//         "updating φ expression arguments in block {}",
//         basic_block.get_index()
//     );
//     basic_block.iter_mut().for_each(|stmt| {
//         match stmt {
//             // φ statement found.
//             Substitution {
//                 var: name,
//                 rhe: Phi { args, .. },
//                 ..
//             } => {
//                 // If the variable name has already been converted to SSA form we need to drop the index.
//                 let name = get_variable_name(name);
//                 trace!("φ statement for variable '{name}' found");
//
//                 if let Some(version) = env.get_variable(&name) {
//                     // If the argument list does not contain the SSA variable we add it.
//                     if args.iter().all(|arg| {
//                         !matches!(
//                             arg,
//                             Variable {
//                                 name: n,
//                                 version: Some(v),
//                                 ..
//                             } if n == &name && v == version
//                         )
//                     }) {
//                         args.push(Variable {
//                             meta: Meta::new(0, 0),
//                             name,
//                             access: Vec::new(),
//                             version: Some(version.clone()),
//                         });
//                     }
//                 }
//             }
//             _ => {
//                 // Since φ statements proceed all other statements we are done here.
//                 return;
//             }
//         }
//     });
// }
//
// /// Traverses the dominator tree in pre-order and for each block, the function
// ///
// ///     1. Renames all variables to SSA form, keeping track of the current
// ///        version of each variable.
// ///     2. Updates φ expression arguments in each successor of the current
// ///        block.
// pub fn insert_ssa_variables(
//     param_data: &mut ParameterData,
//     basic_blocks: &mut Vec<BasicBlock>,
//     dominator_tree: &DominatorTree<BasicBlock>,
// ) -> Result<()> {
//     let mut env = SSAEnvironment::new();
//     for param_name in param_data.iter() {
//         env.add_variable(param_name, 0);
//     }
//     insert_ssa_variables_impl(0, basic_blocks, dominator_tree, &mut env)?;
//     for param_name in param_data.iter_mut() {
//         *param_name = get_ssa_variable_name(param_name, 0);
//     }
//     Ok(())
// }
//
// fn insert_ssa_variables_impl(
//     current_index: Index,
//     basic_blocks: &mut Vec<BasicBlock>,
//     dominator_tree: &DominatorTree<BasicBlock>,
//     env: &mut SSAEnvironment,
// ) -> Result<()> {
//     // 1. Update variables in current block.
//     let successors = {
//         let current_block = basic_blocks
//             .get_mut(current_index)
//             .expect("invalid block index during SSA generation");
//         *current_block = visit_basic_block(current_block, env)?;
//         current_block.get_successors().clone()
//     };
//
//     // 2. Update phi statements in successor blocks.
//     for successor_index in successors {
//         let successor_block = basic_blocks
//             .get_mut(successor_index)
//             .expect("invalid block index during SSA generation");
//         update_phi_statements(successor_block, env);
//     }
//     // 3. Update dominator tree successors recursively.
//     for successor_index in dominator_tree.get_dominator_successors(current_index) {
//         insert_ssa_variables_impl(
//             successor_index,
//             basic_blocks,
//             dominator_tree,
//             &mut env.clone(),
//         )?;
//     }
//     Ok(())
// }
//
// fn visit_basic_block(basic_block: &BasicBlock, env: &mut SSAEnvironment) -> Result<BasicBlock> {
//     trace!(
//         "renaming variables to SSA form in block {}",
//         basic_block.get_index()
//     );
//     let mut stmts: Vec<Statement> = Vec::new();
//     for stmt in basic_block.get_statements() {
//         stmts.push(visit_statement(stmt, env)?)
//     }
//     let mut basic_block = BasicBlock::from_raw_parts(
//         basic_block.get_index(),
//         basic_block.get_meta().clone(),
//         stmts,
//         basic_block.get_predecessors().clone(),
//         basic_block.get_successors().clone(),
//     );
//     basic_block.cache_variable_use();
//     Ok(basic_block)
// }
//
// fn visit_statement(stmt: &Statement, env: &mut SSAEnvironment) -> Result<Statement> {
//     trace!("converting '{stmt}' to SSA");
//     use Statement::*;
//     match stmt {
//         IfThenElse {
//             meta,
//             cond,
//             if_true,
//             if_false,
//         } => Ok(IfThenElse {
//             meta: meta.clone(),
//             cond: visit_expression(cond, env)?,
//             if_true: if_true.clone(),
//             if_false: if_false.clone(),
//         }),
//         Return { meta, value } => Ok(Return {
//             meta: meta.clone(),
//             value: visit_expression(value, env)?,
//         }),
//         Declaration {
//             meta,
//             xtype,
//             name,
//             dimensions,
//             is_constant,
//         } => {
//             use SignalType::*;
//             use VariableType::*;
//             let name = match xtype {
//                 Var => {
//                     // A declaration is always the first occurrence of the variable.
//                     // The variable is only added no the environment on first use.
//                     let ssa_name = get_ssa_variable_name(name, 0);
//
//                     trace!("replacing (declared) variable '{name}' with SSA variable '{ssa_name}'");
//                     ssa_name
//                 }
//                 Component => {
//                     env.add_component(name, ());
//                     name.clone()
//                 }
//                 Signal(Input, _) => {
//                     env.add_input(name, ());
//                     name.clone()
//                 }
//                 Signal(Output, _) => {
//                     env.add_output(name, ());
//                     name.clone()
//                 }
//                 Signal(Intermediate, _) => {
//                     env.add_intermediate(name, ());
//                     name.clone()
//                 }
//             };
//             Ok(Declaration {
//                 meta: meta.clone(),
//                 xtype: xtype.clone(),
//                 name,
//                 dimensions: dimensions.clone(),
//                 is_constant: is_constant.clone(),
//             })
//         }
//         Substitution {
//             meta,
//             var,
//             access,
//             op,
//             rhe,
//         } => {
//             // We need to visit the right-hand expression before updating the environment.
//             let rhe = visit_expression(rhe, env)?;
//             let var = match op {
//                 AssignOp::AssignVar => {
//                     // If this is the first assignment to the variable we set the version to 0.
//                     let version = env
//                         .get_variable(&var)
//                         .map(|&version| version + 1)
//                         .unwrap_or_default();
//                     env.add_variable(&var, version);
//                     let ssa_var = get_ssa_variable_name(var, version);
//
//                     trace!("replacing (written) variable '{var}' with SSA variable '{ssa_var}'");
//                     ssa_var
//                 }
//                 _ => var.clone(),
//             };
//             Ok(Substitution {
//                 meta: meta.clone(),
//                 var,
//                 access: access.clone(),
//                 op: op.clone(),
//                 rhe,
//             })
//         }
//         ConstraintEquality { meta, lhe, rhe } => Ok(ConstraintEquality {
//             meta: meta.clone(),
//             lhe: visit_expression(lhe, env)?,
//             rhe: visit_expression(rhe, env)?,
//         }),
//         LogCall { meta, arg } => Ok(LogCall {
//             meta: meta.clone(),
//             arg: visit_expression(arg, env)?,
//         }),
//         Assert { meta, arg } => Ok(Assert {
//             meta: meta.clone(),
//             arg: visit_expression(arg, env)?,
//         }),
//     }
// }
//
// /// Replaces each occurrence of the variable `v` with a versioned SSA variable `v.n`.
// /// Currently, signals and components are not touched.
// fn visit_expression(expr: &Expression, env: &SSAEnvironment) -> Result<Expression> {
//     use Expression::*;
//     match expr {
//         InfixOp {
//             meta,
//             lhe,
//             infix_op,
//             rhe,
//         } => Ok(InfixOp {
//             meta: meta.clone(),
//             lhe: Box::new(visit_expression(lhe.as_ref(), env)?),
//             infix_op: infix_op.clone(),
//             rhe: Box::new(visit_expression(rhe.as_ref(), env)?),
//         }),
//         PrefixOp {
//             meta,
//             prefix_op,
//             rhe,
//         } => Ok(PrefixOp {
//             meta: meta.clone(),
//             prefix_op: prefix_op.clone(),
//             rhe: Box::new(visit_expression(rhe, env)?),
//         }),
//         InlineSwitchOp {
//             meta,
//             cond,
//             if_true,
//             if_false,
//         } => Ok(InlineSwitchOp {
//             meta: meta.clone(),
//             cond: Box::new(visit_expression(cond, env)?),
//             if_true: Box::new(visit_expression(if_true, env)?),
//             if_false: Box::new(visit_expression(if_false, env)?),
//         }),
//         Variable {
//             meta,
//             name,
//             access,
//             version,
//         } => {
//             assert!(version.is_none(), "variable already converted to SSA form");
//             match env.get_variable(name) {
//                 Some(version) => {
//                     let var = Variable {
//                         meta: meta.clone(),
//                         name: name.clone(),
//                         access: access.clone(),
//                         version: Some(version.clone()),
//                     };
//                     trace!("replacing (read) variable '{name}' with SSA variable '{var}'");
//                     Ok(var)
//                 }
//                 None => Err(anyhow!(
//                     "failed to convert undeclared variable '{name}' to SSA"
//                 )),
//             }
//         }
//         Signal { meta, name, access } => Ok(Signal {
//             meta: meta.clone(),
//             name: name.clone(),
//             access: access.clone(),
//         }),
//         Component { meta, name } => Ok(Component {
//             meta: meta.clone(),
//             name: name.clone(),
//         }),
//         Number(meta, value) => Ok(Number(meta.clone(), value.clone())),
//         Call { meta, id, args } => {
//             let args = args
//                 .into_iter()
//                 .map(|expr| visit_expression(expr, env))
//                 .collect::<Result<Vec<Expression>>>()?;
//             Ok(Call {
//                 meta: meta.clone(),
//                 id: id.clone(),
//                 args,
//             })
//         }
//         ArrayInLine { meta, values } => {
//             let values = values
//                 .into_iter()
//                 .map(|expr| visit_expression(expr, env))
//                 .collect::<Result<Vec<Expression>>>()?;
//             Ok(ArrayInLine {
//                 meta: meta.clone(),
//                 values,
//             })
//         }
//         Phi { meta, args } => {
//             // φ expression arguments are updated in a later pass.
//             Ok(Phi {
//                 meta: meta.clone(),
//                 args: args.clone(),
//             })
//         }
//     }
// }
//
// // Returns the name (as a `String`) of the SSA variable with the given version.
// fn get_ssa_variable_name(name: &str, version: usize) -> String {
//     use Expression::*;
//     let var = Variable {
//         meta: Meta::new(0, 0),
//         name: name.to_string(),
//         access: Vec::new(),
//         version: Some(version),
//     };
//     format!("{}", var)
// }
//
// // Returns the name of the variable corresponding to the given SSA variable name.
// fn get_variable_name(ssa_var: &str) -> String {
//     ssa_var
//         .rsplit_once('.')
//         .map(|parts| parts.0)
//         .unwrap_or(ssa_var)
//         .to_string()
// }
//
