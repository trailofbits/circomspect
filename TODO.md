# TODO

  - [x] Implement a basic block type, and functionality allowing us to lift the
        AST to a CFG.
  - [x] Implement `vars_read`, `vars_written`, `signals_read`,
        `signals_written`, and `signals_constrained` on `Statement`.
  - [x] Compute dominators, dominator frontiers, and immediate dominators on
        basic blocks. (See _A Simple, Fast Dominance Algorithm_.)
  - [x] Implement (pruned) SSA.
  - [ ] Implement analyses enabled by SSA:
      - [x] Constant propagation
          - [x] Implement constant propagation.
          - [x] Implement/update `is_constant` and `value` on `Expression`.
      - [x] Dead code analysis
      - [ ] Value-range analysis (simple overflow detection)
      - [x] Intraprocedural data flow
      - [x] Unconstrained signals (simple)
  - [ ] Implement emulation.
      - [ ] Unconstrained signals (specific)
  - [ ] Implement symbolic execution.
      - [ ] Unconstrained signals (complete)
      - [ ] Overflow detection (complete)


# Potential issues

 - [x] Bit level arithmetic does not commute with modular reduction. This means that
     - Currently, `(p | 1) - 1 != 0` (see `circom_algebra/src/modular_arithmetic.rs`)
     - `!x` (256-bit complement) will typically overflow which means that `!x`
       does not satisfy `(!x)_i = x_i ^ 1` for all `i`.

 - [x] Arithmetic is done in `(p/2, p/2]` which may produce unexpected results.
     - E.g. `p/2 + 1 < p/2 - 1`.

 - [ ] Typically you want to constrain all input and output signals for each
       instantiated component in each circuit. There are exceptions from this
       rule (e.g. the circomlib `AliasCheck` template). We should add an
       analysis pass ensuring that signals belonging to instantiated
       subcomponents are properly constrained.

 - [ ] Find cases when it is possible to prove that the output from a component
       is not uniquely determined by the input.
