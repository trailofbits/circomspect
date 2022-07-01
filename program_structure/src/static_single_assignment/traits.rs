use log::trace;
use std::collections::HashSet;

use super::errors::SSAResult;

pub type Version = usize;
pub type VariableSet = HashSet<String>;

pub trait SSAEnvironment {
    // Enter variable scope.
    fn add_variable_block(&mut self);

    // Leave variable scope.
    fn remove_variable_block(&mut self);
}

pub trait SSABasicBlock<Environment: SSAEnvironment>: DirectedGraphNode {
    type Statement: SSAStatement<Environment>;

    // type Iter: Iterator<Item = &'a <Self as SSABasicBlock<'a>>::Statement>;
    // type IterMut: Iterator<Item = &'a mut Self::Statement>;

    /// Add the given statement to the front of the basic block.
    fn insert_statement(&mut self, stmt: Self::Statement);

    /// Returns an iterator over the statements of the basic block.
    ///
    /// Note: We have to use dynamic dispatch here because returning `impl
    /// Trait` from trait methods is not a thing yet. For details, see
    /// rust-lang.github.io/impl-trait-initiative/RFCs/rpit-in-traits.html)
    fn get_statements<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Statement> + 'a>;

    /// Returns an iterator over mutable references to the statements of the
    /// basic block.
    ///
    /// Note: We have to use dynamic dispatch here because returning `impl
    /// Trait` from trait methods is not a thing yet. For details, see
    /// rust-lang.github.io/impl-trait-initiative/RFCs/rpit-in-traits.html)
    fn get_statements_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut Self::Statement> + 'a>;

    /// Returns the set of variables written by the basic block. Since we don't
    /// want to pollute the general SSA traits with Circom internal types we use
    /// strings to represent variable names here.
    fn get_variables_written(&self) -> VariableSet {
        self.get_statements()
            .fold(HashSet::new(), |mut vars, stmt| {
                vars.extend(stmt.get_variables_written());
                vars
            })
    }

    /// Returns true if the basic block has a phi statement for the given
    /// variable.
    fn has_phi_statement(&self, name: &str) -> bool {
        self.get_statements()
            .any(|stmt| stmt.is_phi_statement_for(name))
    }

    /// Inserts a new phi statement for the given variable at the top of the basic
    /// block.
    fn insert_phi_statement(&mut self, name: &str) {
        self.insert_statement(SSAStatement::new_phi_statement(name));
    }

    /// Updates the RHS of each phi statement in the basic block with the SSA
    /// variable versions from the given environment.
    fn update_phi_statements(&mut self, env: &Environment) {
        trace!(
            "updating phi expression arguments in block {}",
            self.get_index()
        );
        for stmt in self.get_statements_mut() {
            if stmt.is_phi_statement() {
                stmt.ensure_phi_argument(env);
            } else {
                // Since phi statements proceed all other statements we are done
                // here.
                break;
            }
        }
    }

    /// Updates each variable to the corresponding SSA variable, in each
    /// statement in the basic block.
    fn insert_ssa_variables(&mut self, env: &mut Environment) -> SSAResult<()> {
        trace!("inserting SSA variables in block {}", self.get_index());
        for stmt in self.get_statements_mut() {
            stmt.insert_ssa_variables(env)?;
        }
        Ok(())
    }
}

pub trait SSAStatement<Environment: SSAEnvironment>: Clone {
    /// Returns the set of variables written by statement. Since we don't want
    /// to pollute the general SSA traits with Circom internal types we use
    /// strings to represent variable names here.
    fn get_variables_written(&self) -> VariableSet;

    /// Returns a new phi statement (with empty RHS) for the given variable.
    fn new_phi_statement(name: &str) -> Self;

    /// Returns true iff the statement is a phi statement.
    fn is_phi_statement(&self) -> bool;

    /// Returns true iff the statement is a phi statement for the given variable.
    fn is_phi_statement_for(&self, name: &str) -> bool;

    /// Ensure that the phi expression argument list of a phi statement contains the
    /// current version of the variable, according to the given environment.
    ///
    /// Panics if the statement is not a phi statement.
    fn ensure_phi_argument(&mut self, env: &Environment);

    /// Replace each variable occurring in the statement by the corresponding
    /// versioned SSA variable.
    fn insert_ssa_variables(&mut self, env: &mut Environment) -> SSAResult<()>;
}

pub type Index = usize;
pub type IndexSet = HashSet<Index>;

/// This trait is used to make graph algorithms (like dominator tree and dominator
/// frontier generation) generic over the graph node type for unit testing purposes.
pub trait DirectedGraphNode {
    fn get_index(&self) -> Index;

    fn get_predecessors(&self) -> &IndexSet;

    fn get_successors(&self) -> &IndexSet;
}
