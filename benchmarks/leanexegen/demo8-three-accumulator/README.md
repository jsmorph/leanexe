# Demo 8 three-accumulator benchmark

Demo 8 is an out-of-sample scalar-loop case generated from a new prose request on 2026-08-09.  Its public function is the identity on `Array UInt64`, while a singleton passes through a scalar helper with remaining, result, and audit accumulators.  The loop decrements remaining, increments result, and adds two to audit before returning result.

The compiler emitted a 1,793-byte WASM module with SHA-256 digest `932262dad153458571234372e49c4142d7a7ea82cff4d09e2f2fd5eb276e4151`.  Function zero has 23 locals, accumulator coordinates `[4, 5, 6]`, and result slot two.  This layout differs from Demo 7's 15-local, two-accumulator function and tests whether the annotation consumer discovers the counter pair from transition semantics.

The generated recipe selected `function_0_scalar_post_test_loop_0_terminates_with_counter_transfer_identity`, and the proof agent used it on its first edited candidate.  Stage 5 completed in 313.253 seconds, including 223.242 seconds in Codex and 75.717 seconds in outer acceptance, while the accepted proof contains 70 lines.  A separate `tools/leanexegen verify -s` run accepted the package.

`current-1` preserves the complete generated package, journal, telemetry, recipe, checked annotation module, and exact artifact proof.  This single run supplies out-of-sample structural evidence rather than a comparative timing distribution.  The [timing record](timings.json) records its monotonic intervals and proof structure.
