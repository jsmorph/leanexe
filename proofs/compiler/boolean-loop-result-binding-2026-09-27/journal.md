# Boolean loop-result bindings

Ordinary Boolean lets and standard Id binds now try the existing scalar-value /
loop-body path first, then bind a recursively extracted Boolean loop result to
a scalar Boolean tail. The lazy fallback follows failure of the whole previous
path: a scalar-extractable value can also supply a zero-iteration loop plan when
the body itself contains no loop. Successful previous candidates keep priority.

The new source evaluation and support constructors independently describe a
Boolean loop action followed by a converted scalar tail. Totality, extraction
acceptance and support recovery pass on the first build. A separate small
combinator proves the two success cases. The loop-result proof retains count,
initial value, step and exit conditions, and evaluates the new result with the
Boolean binding at the final store. No WASM lowering changes are required.
The first build reported two unused simp arguments, removed before the next run.

All correctness, invariant and public WASM admission proofs pass on the first
build. All ten native examples pass 240 comparisons. An additional test control
initially assumed every all-scalar conditional also passes scalar extraction.
The diagnostic isolated retained Id annotations on the conditional result: those
cases use the range-choice parser and are still accepted by the new binding.
The control now checks the overlapping paths for the unannotated conditionals;
annotated cases still run both public and direct evaluation checks. The original
fixture and failure logs are preserved.

The final raw syntax tests pass 64,512 comparisons, 34,560 invalid-input checks
and 2,304 equivalent-binding controls. Native fixtures add 240 comparisons.
Raw tests exercise both public extraction and direct plan execution, binder
annotations, both argument orders, loop exit modes, mixed scalar/loop choices,
Id wrappers, and further Boolean expressions after the bound result.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1306 declarations.
