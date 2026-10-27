use parser::hir::{AccessPath, AccessStep, ArrayIndex, HirProject};

pub(crate) fn path(hir: &HirProject, name: &str, index: Option<usize>) -> AccessPath {
    let symbol = hir.symbols().iter().find(|symbol| symbol.name == name).unwrap();
    let mut steps = Vec::new();
    if let Some(index) = index {
        steps.push(AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: symbol.span,
        });
    }
    AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps,
        component_input: false,
        component_output: false,
        span: symbol.span,
    }
}
