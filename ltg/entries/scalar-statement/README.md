# Checked scalar expression and statement execution

`ScalarTransition.Expr.program_spec` and `Stmt.program_spec` prove the
instruction programs of typed scalar descriptors from their checked
evaluator results.  Statements cover assignments, sequences, and
conditionals.  Expressions cover the supported word operations and
Boolean conditions.  These theorems accept an arbitrary continuation
and preserve the complete store.

`Stmt.program_frame_spec` adapts statement execution to the `Locals`
frames used by array proofs.  It requires empty initial and final
operand stacks.  `State.ofLocals_get` connects the evaluator to the
existing getter equations, while `State.ofLocals_result_set` connects
an internal assignment to `FixedArrayFold.resultFrame`.  The shared
frame adapter checked in 64 seconds with standard axioms.  Its first
draft omitted the explicit Frame import required by the frame-extensionality
proof.

Supply the exact descriptor-region equality before applying execution.
For statement sequences, prove the evaluator result of each assignment
and compose those results through the existing sequence evaluator.
`Stmt.eval_preserves_below` preserves a getter below the scratch boundary
when the descriptor's computed write set excludes its index.

The Riemann append-count consumer uses three assignments: total length
and the two seven-word copy counts.  Its descriptor targets the emitted
instructions 74 through 85.  The word operations retain WASM wrapping
semantics.  Natural-array bounds remain obligations of the caller.
The entry has no dedicated straight-statement compiler annotation and
remains provisional pending complete initializer and independent artifact
verification.

The count consumer checked in 65 seconds.  Its descriptor equality uses
propext, evaluator result uses propext and Quot.sound, and execution uses
the three standard axioms.  The first evaluator draft rewrote State
getters to raw Locals conditionals before applying its word equations.
Providing those equations at the State type lets the evaluator reduce
without expanding local lists.  The final assignment also required an
explicit resultFrame target before applying its setter theorem.

The append pointer prefix supplies a second scalar-statement consumer.
Its six assignments checked in 45 seconds with standard axioms and
compose with the header loads and count region in the checked 32-instruction
setup.  For that evaluator proof, simplification converted bounded
optional list reads to indexed reads.  The existing
`Frame.parameter_getElem_of_get` and `internal_getElem_of_get` projections
supplied the required equations without enumerating the local vector.
