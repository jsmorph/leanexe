# Scalar post-test loop

Use this entry when the annotation kind is `leanexe.loop.scalar-post-test.v1`.  The checked descriptor records the body statement, exit condition, scratch-local boundary, accumulator frame, entry state, result slot, and post-loop suffix.  Generated `body_eval` and `condition_eval` equations expose compact `UInt64` transitions without repeating scratch-local symbolic execution.

`ScalarTransition.postTestProgram_spec` accepts an application invariant and measure.  `ScalarTransition.CounterTransition.postTestProgram_spec` specializes the loop argument to two counters whose sum is preserved while one counter decreases.  Apply a generated entry or termination adapter first when it already converts the exact artifact function into one of these loop interfaces.

Keep application mathematics separate from descriptor execution.  The descriptor proves what the exact instructions do, while the artifact proof supplies the invariant relating compact state to the requested result.  Journal any missing transition theorem at the level where repeated arithmetic or state reconstruction remains after the descriptor equations have been used.
