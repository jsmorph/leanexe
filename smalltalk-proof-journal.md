# Smalltalk proof journal

## Concrete memory and allocation (2026-10-06)

The earlier Smalltalk proofs describe separate lists; they do not justify the
array implementation. `Project.Smalltalk.Memory` now checks read-after-write,
unchanged reads at other indices, and the address arithmetic used by the VM.
The capacity limit and positive handle bound are explicit: without those bounds
UInt64 subtraction and addition can wrap. The first arithmetic attempt omitted
the handle upper bound from the local arithmetic facts and failed. Naming that
bound lets `omega` prove both intermediate products and final addresses are
smaller than 2^64. The core array lemmas suffice; no imported WASM proof is
needed.

`allocateCell_read` checks the complete write sequence against a separate
word-level postcondition. `allocateCell_field` then proves exactly what the
new cell contains, and `allocateCell_preserves_other` proves all eight words of
every other valid cell are unchanged. `allocateCell_register` and
`allocateCell_shape` check the register effects and unchanged arena layout.
The shared address equality lemma avoids repeating UInt64 arithmetic in these
proofs. Enumerating the eight possible offsets required converting word
equalities to Nat equalities before `omega`; asking it to derive the word
disjunction directly failed.

These results assume a valid free-head handle. They do not establish free-list
membership or count, collector reachability, VM instruction semantics, or WASM
correctness. The Smalltalk driver now builds the proof imports and reports
axioms for the main concrete theorems before running the existing execution
checks.

## Free-list allocation (2026-10-06)

`FreeList.Chain` records the concrete next word of each free cell, valid
handles, and distinct membership. `FreeList.Valid` additionally requires the
actual count and exact agreement between zero tags and list membership.
`allocate_valid` now proves that the checked allocator preserves shape and
this complete free-list invariant while removing one head. Allocating a zero
tag is excluded explicitly; otherwise completeness would be false.
`allocate_empty_preserves_cells` checks the error path and proves that all
cell words remain unchanged when the valid list is empty.

Direct case analysis on a chain indexed by `read s 8` failed because dependent
elimination attempted to resolve the array read against zero. The generic
`chain_cons` and `chain_nil` inversion lemmas avoid that problem. The previously
checked cell-preservation and register-effect lemmas then suffice for the
allocation proof; no executable definition changed. These theorems assume
free-list validity before allocation. Initialization and collection still
need proofs that establish it.

## Complete sweep (2026-10-06)

`reclaim_read`, `reclaim_field`, and `reclaim_register` check the actual writes
made by reclamation. The collector's sweep preserves mark words and arena
shape. `finishCollection_preserves_marked` applies an invariant through the
actual bounded loop and proves that all eight words of each marked cell remain
unchanged, including after the final statistics write.

`SweepList.Prefix` records precisely which unmarked handles have been visited,
the concrete linked list, its count, unchanged mark words, and a count bound
that rules out integer wraparound. `counted_index` establishes that the loop
visits all handles through capacity. `finishCollection_freeList` then proves
that the result has a complete free list containing exactly the original
unmarked handles, each once. It assumes marked cells have nonzero tags; this
is the condition the marking proof must supply.

The initial audit permitted only `propext` and `Quot.sound`. The new arithmetic
proofs also use `Classical.choice` through generated `omega` proof terms. The
audit now permits these three standard Lean axioms and still rejects every
other axiom, including `sorryAx`. This is recorded in the public proof limits;
the executable implementation and its tests are unchanged. The sweep theorem
does not establish reachability or correctness of the full `collect` call.

## Clearing, enqueue, and reachability specification (2026-10-06)

`cleared` is the exact first loop of `collectReady`, without a new executable
implementation. Its checked results establish zero marks, unchanged payloads
and registers, and preserved shape. The same counted-loop lemma used for
sweeping proves that clearing reaches every handle. One failed arithmetic
goal treated a pair projection as a separate number; reducing the projection
before `omega` resolved it.

The worklist address lemmas establish bounds, distinct indices, and separation
from all registers and cell words. `markReady_read` checks the three concrete
writes. Its payload and worklist results prove that enqueue marks the selected
cell, stores its handle at the old count, increments that count, and preserves
existing worklist entries and every payload. `mark_new` and `mark_old` connect
these facts to the checked `mark` entry point. Implicit worklist-index arguments
had to be supplied before arithmetic tactics could discharge their bounds.

`Graph.Reachable` is an independent path definition from the six actual roots.
Its edges include only the pointer fields, not scalar identifiers or integer
payloads. `sweep_correct` composes exact marking with the concrete sweep to
preserve reachable payloads and free exactly the unreachable handles. The
remaining marking proof must establish exact marking, bounded queue use, and
termination of the actual scan loop. The conditional theorem does not prove
those obligations. All new theorems pass the axiom audit.

## Concrete worklist and root-marking invariant (2026-10-06)

`Worklist.Represents` relates the actual count and every used worklist word to
the pending list. `enqueue_represents` checks append at the old count and
preservation of every existing entry. `handles_length` uses a finite list of
valid handles to bound the number of distinct handles by capacity. Consequently
`enqueue_room` proves that a new unmarked handle cannot encounter a full
pending list. It does not assume spare space.

`MarkInvariant.Holds` connects array payloads, registers, mark words, distinct
scanned and pending handles, reachability, and closure of scanned edges.
`mark_holds` checks the actual `mark`, including zero, existing-mark, and new
mark cases. The new case derives space from the worklist bound and preserves
all graph facts. `initial_holds` establishes the invariant after clearing and
resetting the count; `roots_holds` checks the actual `markRoots` and shows that
every root is in the pending list. The scan loop and its capacity bound remain
unproved.

Two elaboration failures were resolved locally: generic indexing lemmas needed
their list arguments explicitly, and rewriting the proposition inside an `if`
required `simp only` so its dependent decision instance was transported too.
These are proof changes; no executable definition changed. The main results
and all their dependencies pass the axiom audit.

## Concrete scan step (2026-10-06)

`top_word` and `pop_represents` check the actual worklist read and decrement,
including subtraction and address bounds. `scanCell_eq` relates the concrete
scan to marking the exact pointer-field list. `edge_pointers` connects that
list to the independent graph-edge definition for every valid cell tag.

The original combined invariant required closure for every scanned cell at
every intermediate point. That condition is premature immediately after pop,
before marking its children. Closure is now a separate `Closed` predicate;
the basic `Holds` facts still cover payloads, registers, worklist contents,
distinct membership, mark words, and reachability. `scan_holds` proves that a
whole scan preserves those facts, moves exactly one distinct pending handle
to the scanned list, preserves prior marked membership, and establishes
closure for the new scanned cell. It permits cycles and repeated pointers.
The complete scan-loop termination and reachability proof remains to be done.

The full driver passed with the accumulated proof gate: 136 native executions,
181 WASM checks, and all CLI checks. The WASM hash remains
`423aaec2687c65c9993160400cad47efe89f62cfb42d6e2d3095cef90b76b19e`.

## Complete concrete collector (2026-10-06)

`go_finish` proves that the actual scan loop drains its queue within capacity.
Each scan moves one distinct pending handle to the scanned list. The number
of distinct valid handles is at most capacity, so exhausting capacity with a
nonempty queue is impossible. Root coverage and closure at an empty queue
give reachability completeness; the invariant already gives soundness.
`marking_correct` consequently establishes exact marks, an empty worklist,
unchanged payloads, and unchanged non-worklist registers for the actual
clearing, root-marking, and scan passes.

`collectReady_eq_finish` and `collect_eq_finish` connect those passes to the
actual collector definitions, including their error checks and final sweep.
`collect_correct` proves unchanged reachable handles, tags, and payloads;
preserved arena shape; and a complete distinct free list containing exactly
the unreachable handles, with its correct count. `collect_register` checks
the unaffected registers, and `collect_error_unchanged` checks error-phase
behavior. The assumptions are a well-formed typed heap and a phase other than
4. Cycles, repeated pointers, arbitrary initial marks, and any old free list
are permitted. Exact marking and queue space are conclusions, not assumptions.

The proofs remain about the Lean implementation. They do not prove that VM
instructions establish the heap assumptions, that the compiler is correct,
or that the emitted WASM preserves Lean semantics. Those obligations are
distinct from the collector theorem.

## Concrete frames, traversal, and fuel (2026-10-06)

`Frame.lean` checks the exact retirement and advance write sequences, cell
effects, unchanged registers, and preserved shape. Retirement preserves the
method, enclosing activation, and slots while setting the PC to dead and
clearing caller and operands. These results refer to the concrete array
operations, not the earlier separate activation model.

`Traversal.Path` represents actual tagged cells and next words. `walk_path`
and `lexical_path` prove selection from those paths, with zero after the end
and the actual capacity clamp. The path proof requires a nonzero tag so a
zero handle terminates traversal; the VM's tags 7 and 5 satisfy that condition.

`run_eq_iterate` proves equivalence between the fuelled loop and repeated VM
steps, since finished and error states are absorbing. `run_resume` proves
exact state equality under fuel splitting, with an explicit no-wrap bound on
the fuel sum. These are control and fuel facts, not a proof of instruction
semantics or of the VM establishing the collector's heap assumptions.

## Heap validity after collection (2026-10-06)

`collect_allocated` connects nonzero tags after collection to original
reachability. `collect_valid` proves that the resulting heap meets all the
typed-heap assumptions: its roots are retained, every outgoing pointer names
a retained allocated cell, and retained tags remain valid. `collect_reachable`
proves equality of reachability before and after collection. The phase is
unchanged, so another collection is justified and preserves the same live
payloads. Free-list order and statistics are not claimed to be identical.

The first check exposed two unavailable convenience names in the minimal
imports (`not_not` and `by_contra`). An explicit `Classical.byContradiction`
proof checked successfully. No executable definitions changed. These lemmas
support repeated collection; VM initialization and instructions still need
to establish the initial heap assumptions.

## Concrete call-chain and return control (2026-10-06)

`Loops.applyN` and `loop_constant` connect the actual constant-step `loop` to
forward iteration. `onChain_correct` proves exact membership in a represented
caller chain within capacity. `home_correct` proves first eligible lexical
home selection, including retired homes: liveness belongs to the return
check, not the home search. `ReturnChecks` proves underflow, dead-target and
absent-target rejection, and acceptance of a live activation in the caller
chain, using the concrete fields and decisions.

An initial return proof exceeded the elaboration heartbeat limit while
converting a large unfolded expression. The checked `ret_eq` lemma divides
that boundary and makes each branch a direct Boolean rewrite. Broad
simplification with `eq_comm` also recursed; explicit Boolean equalities and
`Bool.decide_or` avoided that problem. No limit was raised. The journal keeps
these failures because the small helpers, rather than more unfolding, made
the proofs check.

`Unwind.Prefix` describes actual caller links through the return target, with
valid distinct handles. `unwind_go_prefix` proves exact retirement and a zero
cursor within its explicit fuel bound. `returnReady_prefix` connects the
result to the actual return function. `retireMany_field` checks all cell
effects, including preserved lexical links and slots; companion results
preserve registers and shape. Pair-pattern lambdas initially differed from
projection lambdas during rewriting. Stating the loop theorem with the
executable function's pair patterns removed that mismatch.

Remaining obligations include returned-value delivery, method lookup,
instruction semantics, and initialization and step preservation of the heap
and chain assumptions. No executable definitions changed in this increment.

## Returned-value delivery (2026-10-06)

`returnCallerReady_field` and `returnCallerReady_register` prove all cell
and register effects of the concrete allocation and delivery writes.
`returnCallerReady_delivers` proves a fresh operand link containing the value
and the old stack, current set to caller, and unchanged caller PC. Freshness
follows from the valid free list and the caller's nonzero activation tag.
`returnCaller_finished` checks phase 3, current zero, and the result register.

`retireMany_free` proves that retirement preserves the free list.
`returnReady_delivers` combines the actual unwind loop with delivery, assuming
a nonempty free list and a caller outside the retired prefix.
`returnReady_finished` combines unwind with the no-caller result. These are
theorems about actual array operations. Reservation before return and VM
preservation of the initial assumptions remain separate obligations.

The checks needed explicit arguments for the returned value and an explicit
lambda for the field theorem's handle and offset. A bare partially applied
theorem did not infer those implicit parameters. No execution code changed.

## Reservation preserves live data (2026-10-06)

`Heap.Valid` pairs graph validity with existence of a complete free list.
Error writes preserve graph validity, free-list validity, payloads, and
reachability; only phase and error registers change. `Reservation.Effect`
states the collector's live-payload, reachability, register, and heap effects.
Its composition lemma handles both possible collections in reservation.

`reserve_correct` proves the actual reservation either preserves the original
phase and provides at least the requested free cells, or reports phase 4
with reason 9. Both outcomes preserve heap and free-list validity, every
original reachable payload, and the reachability relation. `reserve_register`
checks the unaffected registers; already-error inputs are unchanged.
No spare-space assumption is needed for this result. The complete free list
is an input assumption because reservation can leave the heap unchanged.

The first heap proof needed an explicit type on an unused non-mark parameter;
after that annotation, heap and reservation checked without further changes.
Initialization and instruction preservation of `Heap.Valid`, and the
composition of reservation with the return and allocation proofs, remain.

## Returns with possible collection (2026-10-06)

`prefix_reachable` proves reachability of each frame in the represented
unwind prefix. Its target's caller is reachable through field 4 when nonzero.
`reserve_prefix` therefore transfers the same prefix through actual
reservation, including a possible collection or out-of-memory result.
`returnReserved_delivers` combines that transfer with concrete unwind and
delivery. It either reports error 9 before unwinding or delivers the value
in a valid new operand link above the caller's original stack, with unchanged
caller PC. The complete free list and the requested count supply the new link.

`reserve_zero` proves that a zero-cell request leaves the array unchanged.
`returnReserved_finished` consequently needs no free-cell assumption.
`ret_delivers` and `ret_finished` connect these results to the actual public
return function and its live-target, caller-chain, and stack checks. They
cover the same selected-target operation for local and nonlocal returns.
The represented-chain and valid-heap hypotheses remain explicit; the VM has
not yet been proved to establish them for every execution.

The first composition check hit a heartbeat limit in a broad contradiction
search over the expanded runtime state. A separately checked `free_head`
lemma derives a nonempty free list from one available cell and removes that
elaboration boundary. The parameter name `prefix` also failed because it is
a Lean keyword; the declarations use `unwindPath`. No limits were raised and
no executable definitions changed.
