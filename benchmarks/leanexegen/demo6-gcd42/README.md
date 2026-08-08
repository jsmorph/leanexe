# Demo 6 GCD-loop benchmark

Demo 6 is a held-out scalar-loop case generated from a prose request on 2026-08-08.  Its public function maps a singleton `Array UInt64` containing `x` to a singleton containing `gcd(x, 42)` and preserves every other array length.  The generated source implements the scalar calculation as an imperative Euclidean remainder loop in a separate `UInt64 → UInt64` helper.

The baseline package binds a 1,770-byte WASM module with SHA-256 digest `8126a2d03d514dd1335250b05fc9a1f9b89b84b55cc5b4d3e5a019c0ca6599cf`.  Independent `leanexegen verify -s` accepted its exact-artifact theorem.  Stage 5 took 1,056.072 seconds, including 954.785 seconds in Codex and 88.670 seconds in outer acceptance.

The compiler annotated the complete singleton-array wrapper, length dispatch, and direct call, but emitted no region for the scalar helper's loop.  The accepted 191-line proof therefore uses one raw `wp_loop_cons`, one `wp_run`, and seventeen explicit `wp_iff_cons` applications to recover the emitted transition.  Its journal records nine scalar edits before the Euclidean invariant and measure were accepted, after which `FixedArraySingletonWrapper.wrapperProgram_spec` closed the public wrapper without revision.

`dump-ir` identifies the missing compiler form as `Expr.loopFoldMultiSlot` nested beneath a scalar assignment.  The existing loop-fold recognizer handles only a top-level `Stmt.loopFoldMultiSlotAssign`, while the checked scalar-while path handles `Stmt.while`.  The next controlled iteration will add artifact-checked assistance for the expression form and reprove the same package without changing its specification, source, or WASM bytes.
