# Proof Kit PoC

Import `Project.ProofKit.Control` when a theorem proves `Wasm.TerminatesWith` for a generated function definition that is definitionally equal to the selected module function.  The tactic `wp_entry functionDef as initial'` applies `Wasm.TerminatesWith.of_wp_entry` with `rfl` and introduces the initial local frame under the supplied name.  It leaves the function-body weakest-precondition goal visible, so the artifact proof still states and proves the complete semantic result.

```lean
import Project.ProofKit.Control

theorem example : Wasm.TerminatesWith env module_ index initial arguments post := by
  wp_entry Generated.funcDef as initial'
  unfold Generated.funcDef Generated.func
  wp_run
```

## Block-wrapped loops

Use `wp_block_loop invariant inv decreasing measure` after symbolic execution reaches a WebAssembly `block` whose first instruction is a `loop`.  The tactic applies the Talos block and loop rules while keeping both semantic arguments explicit.  This shape occurs in generated scalar loops and in nested loops within larger functions.

Use `wp_entry_to_loop functionDef unfolding functionBody as initial'` when the function entry unfolds and symbolically executes directly to a block-wrapped loop.  This composition performs the entry conversion, unfolds the generated function definition and body, runs the straight-line prefix, and applies the block rule.  The next goal takes `Wasm.wp_loop_cons`, so the proof supplies its invariant and decreasing measure explicitly.

```lean
theorem loop_correct : Wasm.TerminatesWith env module_ index initial arguments post := by
  wp_entry_to_loop Generated.func0Def
    unfolding Generated.func0
    as initial'
  apply Wasm.wp_loop_cons
    (Inv := loopInvariant initial' input)
    (μ := loopMeasure)
  · exact invariant_initial
  · exact invariant_preserved_and_measure_decreases
```

## Single-call entry wrappers

Use `wp_entry_single_call functionDef unfolding functionBody as initial' using callProof` when an entry function executes straight-line code, makes one direct call, and returns that call's result.  The tactic performs the entry conversion, unfolds and executes the wrapper, applies `Wasm.wp_call_tw` to the supplied call theorem, and executes the return continuation.  The call theorem remains an explicit argument, while Lean rejects wrappers whose generated control flow does not match this shape.

```lean
theorem wrapper_correct : Wasm.TerminatesWith env module_ index initial args post := by
  wp_entry_single_call Generated.funcDef
    unfolding Generated.func
    as initial'
    using callee_correct env initial' input
```
