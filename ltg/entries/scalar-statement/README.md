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
remains provisional pending complete Euler independent artifact verification.

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

`Expr.typedIteProgram_spec` retains the decoded conditional instruction's
parameter and result-type lists.  It applies the existing Talos
control-type equality after executing the descriptor's condition, then
uses the checked descriptor theorem for the selected branch.
`Stmt.typedIteAssignProgram_frame_spec` adds assignment and a Locals-frame
continuation.  Both checked in the same 140-second module build with
standard axioms.  The existing canonical descriptor programs remain
available to consumers whose exact regions match them.
The adapter retains metadata on its outer conditional.  Its condition
and branch programs still use the canonical `Expr.program` form, so a
consumer must check those nested regions as part of its exact equality.

The first two module checks failed in 128 and 100 seconds at the assignment
adapter.  Ordinary evaluator simplification reduced the Option bind.
Passing `rest` explicitly to `localSet_spec` prevented inference of a raw
`List.append [] rest` suffix that the restricted continuation rewrite
left unchanged.  These durations include imports and system I/O.

The extraction stop-index calculation is a checked consumer of the typed
assignment theorem.  Its emitted five-instruction region selects the
requested size when that size is at most the represented array length,
including equality.  The focused module checked in 137 seconds with
standard axioms.  A preceding combined stop/span target reached its
six-minute limit without a consumer diagnostic after building the shared
adapter.  The exact failed draft was retained, and the two calculations
were split before the focused check.

The span calculation and the complete extraction input now use the same
adapter.  Their composition with capacity, allocation, and copying checks
against the current Riemann artifact.  The LTG declaration import check,
package and forest tests, and Lean-backed knowledge promotion test pass.

`Expr.assign_frame_spec` composes expression evaluation and one internal
assignment into `FixedArrayFold.resultFrame`.  Its evaluation premise
requires the expression to preserve the incoming scalar state.  It
accepts arbitrary modules, scratch and destination indices, and
continuations.  Ordinary simplification reduces the evaluator's Option
bind before applying the existing setter theorem.

The current Riemann output uses this theorem for the total length and
both width-one copy counts in function 99.  The exact twelve-instruction
count region composes with pointer/length preparation, capacity,
allocation, copying, and result assignment into both complete
73-instruction concatenation regions.  All consumer and adapter audits
contain only standard axioms.  The entry remains provisional, with no
independent complete Euler package or measured proving-time benefit.
