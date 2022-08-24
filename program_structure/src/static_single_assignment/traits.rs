use log::trace;
use std::hash::Hash;
use std::collections::HashSet;

use super::errors::SSAResult;

pub trait SSAConfig: Sized {
    /// The type used to track variable versions.
    type Version;

    /// The type of a variable.
    type Variable: PartialEq + Eq + Hash + Clone;

    /// An environment type used to track version across the CFG.
    type Environment: SSAEnvironment;

    /// The type of a statement.
    type Statement: SSAStatement<Self>;

    /// The type of a basic block.
    type BasicBlock: SSABasicBlock<Self> + DirectedGraphNode;
}

/// An environment used to track variable versions across a CFG.
pub trait SSAEnvironment {
    /// Enter variable scope.
    fn add_variable_scope(&mut self);

    /// Leave variable scope.
    fn remove_variable_scope(&mut self);
}

/// A basic block containing a (possibly empty) list of statements.
pub trait SSABasicBlock<Cfg: SSAConfig>: DirectedGraphNode {
    /// Add the given statement to the front of the basic block.
    fn prepend_statement(&mut self, stmt: Cfg::Statement);

    /// Returns an iterator over the statements of the basic block.
    ///
    /// Note: We have to use dynamic dispatch here because returning `impl
    /// Trait` from trait methods is not a thing yet. For details, see
    /// rust-lang.github.io/impl-trait-initiative/RFCs/rpit-in-traits.html)
    fn statements<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Cfg::Statement> + 'a>;

    /// Returns an iterator over mutable references to the statements of the
    /// basic block.
    ///
    /// Note: We have to use dynamic dispatch here because returning `impl
    /// Trait` from trait methods is not a thing yet. For details, see
    /// rust-lang.github.io/impl-trait-initiative/RFCs/rpit-in-traits.html)
    fn statements_mut<'a>(
        &'a mut self,
    ) -> Box<dyn Iterator<Item = &'a mut Cfg::Statement> + 'a>;

    /// Returns the set of variables written by the basic block.
    fn variables_written(&self) -> HashSet<Cfg::Variable> {
        self.statements()
            .fold(HashSet::new(), |mut vars, stmt| {
                vars.extend(stmt.variables_written());
                vars
            })
    }

    /// Returns true if the basic block has a phi statement for the given
    /// variable.
    fn has_phi_statement(&self, var: &Cfg::Variable) -> bool {
        self.statements()
            .any(|stmt| stmt.is_phi_statement_for(var))
    }

    /// Inserts a new phi statement for the given variable at the top of the basic
    /// block.
    fn insert_phi_statement(&mut self, var: &Cfg::Variable, env: &Cfg::Environment) {
        self.prepend_statement(SSAStatement::new_phi_statement(var, env));
    }

    /// Updates the RHS of each phi statement in the basic block with the SSA
    /// variable versions from the given environment.
    fn update_phi_statements(&mut self, env: &Cfg::Environment) {
        trace!(
            "updating phi expression arguments in block {}",
            self.index()
        );
        for stmt in self.statements_mut() {
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
    fn insert_ssa_variables(&mut self, env: &mut Cfg::Environment) -> SSAResult<()> {
        trace!("inserting SSA variables in block {}", self.index());
        for stmt in self.statements_mut() {
            stmt.insert_ssa_variables(env)?;
        }
        Ok(())
    }
}

/// A statement in the language.
pub trait SSAStatement<Cfg: SSAConfig>: Clone {
    /// Returns the set of variables written by statement.
    fn variables_written(&self) -> HashSet<Cfg::Variable>;

    /// Returns a new phi statement (with empty RHS) for the given variable.
    fn new_phi_statement(name: &Cfg::Variable, env: &Cfg::Environment) -> Self;

    /// Returns true iff the statement is a phi statement.
    fn is_phi_statement(&self) -> bool;

    /// Returns true iff the statement is a phi statement for the given variable.
    fn is_phi_statement_for(&self, var: &Cfg::Variable) -> bool;

    /// Ensure that the phi expression argument list of a phi statement contains the
    /// current version of the variable, according to the given environment.
    ///
    /// Panics if the statement is not a phi statement.
    fn ensure_phi_argument(&mut self, env: &Cfg::Environment);

    /// Replace each variable occurring in the statement by the corresponding
    /// versioned SSA variable.
    fn insert_ssa_variables(&mut self, env: &mut Cfg::Environment) -> SSAResult<()>;
}

pub type Index = usize;
pub type IndexSet = HashSet<Index>;

/// This trait is used to make graph algorithms (like dominator tree and dominator
/// frontier generation) generic over the graph node type for unit testing purposes.
pub trait DirectedGraphNode {
    fn index(&self) -> Index;

    fn predecessors(&self) -> &IndexSet;

    fn successors(&self) -> &IndexSet;
}
