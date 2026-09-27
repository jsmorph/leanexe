# Scalar word setup before Boolean loops

The preceding monadic loop-result capability passed the complete compiler proof,
nineteen axiom audits and 579 native/V8 comparisons. Its evidence and fixture-name
correction are committed. This increment adds pure scalar word setup before a
Boolean loop body, using exact UInt64 let or standard word-to-Boolean Id bind.

The independent source relation distinguishes scalar setup before the loop from
a loop-valued action followed by a scalar Boolean continuation. Extraction first
tries a scalar action and recursively compiles the body with its lexical binding;
otherwise it retains the checked word-loop action path. Preserved loop-state
bindings carry the setup value across all accumulator/index changes. The public
application and WASM theorem statements remain unchanged.

The source totality, acceptance, supported-source recovery, evaluation and
invariant proofs pass (154 targets). The first build needed parentheses around
the match expression in two theorem statements; no semantic correction was
required. Public application and descriptor admission also pass. Ten native
declarations pass 240 IR comparisons, covering multiple lexical/monadic setup
bindings, count/start/stride captures, helpers within the loop, mixed Boolean
inputs and retained Id input/output annotations.

The raw syntax matrix passes 24,192 native/IR comparisons, 13,824 invalid-input
checks and 1,728 lexical setup controls. It varies setup depth/form, Id annotations,
public argument order, binder info, loops and Boolean tails. Monadic and lexical
setup produce identical IR. Invalid unused setup, unsupported dead setup branches,
wrong binding kinds and bad Boolean continuations are rejected. The initial test
used the reserved notation keyword prefix as a local name; renaming it to
setupSource corrected the fixture. The failed log is preserved.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 599 inputs across 28 declarations, including twenty-two ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1136 declarations.
