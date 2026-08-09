# Demo 8 three-accumulator benchmark

Demo 8 is an out-of-sample scalar-loop case generated from a new prose request on 2026-08-09.  Its public function is the identity on `Array UInt64`, while a singleton passes through a scalar helper with remaining, result, and audit accumulators.  The loop decrements remaining, increments result, and adds two to audit before returning result.

The compiler emitted a 1,793-byte WASM module with SHA-256 digest `932262dad153458571234372e49c4142d7a7ea82cff4d09e2f2fd5eb276e4151`.  Function zero has 23 locals, accumulator coordinates `[4, 5, 6]`, and result slot two.  This layout differs from Demo 7's 15-local, two-accumulator function and tests whether the annotation consumer discovers the counter pair from transition semantics.

The generated recipe selected `function_0_scalar_post_test_loop_0_terminates_with_counter_transfer_identity`, and the proof agent used it on its first edited candidate.  Stage 5 completed in 313.253 seconds, including 223.242 seconds in Codex and 75.717 seconds in outer acceptance, while the accepted proof contains 70 lines.  A separate `tools/leanexegen verify -s` run accepted the package.

The later complete-composition starter applied `FixedArraySingletonWrapper.wrapperProgram_spec` and supplied the generated three-accumulator theorem before Codex began.  The proof agent changed only the invalid-length and singleton result equations, and its first candidate passed.  This run took 477.180 seconds, 52.3 percent longer than the earlier run, and produced a 72-line, 265-word proof, so it confirms structural transfer without showing a Demo 8 timing gain.

`current-1` preserves the initial complete package, while `complete-starter-1` preserves the later package, journal, telemetry, recipe, checked annotation module, and exact artifact proof.  Separate `tools/leanexegen verify -s` runs accepted both packages over the same artifact digest.  The [timing record](timings.json) records their monotonic intervals, proof structure, and comparison result.
