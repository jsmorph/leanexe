# Scheme VM: executable semantics and checked control laws

This document records the abstract-machine milestone. The subsequent concrete
arena VM, collector, and WASM tests are described in [scheme-runtime.md](scheme-runtime.md).

This development starts with the VM alone, based on `deslop` at
`8895946bb15c802171fb5e60899a3e8af9eedf6e`. It accepts hand-assembled instructions.
The executable Lean model and its proofs form a specification for a later LeanExe
WASM implementation. There is no Scheme reader, expander, or compiler in this change.

## Design review

Use one immutable stack containing both operand values and return frames. A frame
saves a return instruction address, the caller's environment, and the rest of the
stack. A continuation value contains a saved stack. There is no separate call stack
or stack-copying operation in the semantic model.

An environment maps numeric names to mutable store locations. A closure captures
that mapping, and a call allocates fresh locations for its parameters. Mutation
changes a location, so closures and saved continuations referring to it see the same
latest value. Resuming a continuation restores control and environments through
its saved frames; it retains the current store.

The machine has explicit `exec`, `apply`, and `returning` states, plus terminal
`done` and `error` states. Every application, including a primitive callback, is a
transition through `apply`. This matters for `call/cc` used as its own callback:
callback application cannot build a native interpreter call chain.

The most consequential choices are:

| Choice | Reason and consequence |
|---|---|
| Unified immutable stack | Pending operands are part of a continuation. Repeated invocation can reuse the same saved stack without consuming it. |
| Separate locations and environments | Continuations restore bindings without rolling back mutation. Recursive closures can refer to their own store location. |
| Explicit ordinary and tail calls | An ordinary call saves one return frame. A tail call passes its existing frame directly to the callee. |
| `call/cc` as a callable value | It is first-class. Its callback receives the current continuation and runs with that same return frame, including in tail position. |
| Checked instruction boundaries | Arguments cannot be popped through a frame. Tail calls and returns reject leftover operands. Missing instructions, bindings, and locations become errors. |
| Total, fuel-bounded runner | Execution can pause at any transition and resume with another fuel slice. Completion and failure are absorbing. |

These choices follow the relevant Scheme control contracts: only `#f` is false,
and `call/cc` must call its callback in tail position. See
[R7RS sections 3.2 and 3.5](https://standards.scheme.org/corrected-r7rs/r7rs-Z-H-5.html)
and [section 6.10](https://standards.scheme.org/corrected-r7rs/r7rs-Z-H-8.html#node_sec_6.10).
This implementation has fixed procedure arities and a single returned value;
multiple values and `dynamic-wind` are outside this milestone.

## Instructions

The top of the stack is written on the left in the following table. `S` denotes the
remaining stack, and `F` denotes either a return frame or the halt boundary.

| Instruction | Effect |
|---|---|
| `push v` | `S` becomes `v :: S`. |
| `load name` | Read the location bound to `name` and push its current value. |
| `store name` | Replace the bound location using the top operand; replace that operand with `unit`. |
| `close entry params` | Push a closure capturing the current environment. |
| `drop` | Remove one operand without crossing a frame. |
| `jump target` | Set the instruction address. |
| `branch target` | Pop a value; branch to `target` for `#f`, otherwise advance. |
| `binary op` | `b :: a :: S` becomes `op a b :: S`. |
| `call n` | Extract `arg_n :: … :: arg_1 :: proc :: S`; apply in source order with a new frame saving `pc + 1`, the caller environment, and `S`. |
| `tailcall n` | Extract the same operands; require `S = F`; apply using `F` itself. |
| `ret` | Require `v :: F`; deliver `v` to `F`. |

Delivery to a frame restores its saved address and environment and pushes the
result above the saved remainder. Delivery to halt finishes. `call/cc` takes one
callback; a continuation takes one result and discards the invoker's stack.
Addresses refer to one persistent code image. Resuming with a different code image
is outside the contract; a future REPL must preserve addresses of live closures and
continuations.

`push` accepts model values, including callable values. This is a typed instruction
API, not a serialized bytecode format. Invalid captured locations and saved
addresses are checked when accessed. The arithmetic operations are wrapping
unsigned `UInt64` addition/subtraction and word comparisons, not Scheme's numeric
tower. Numeric names, `Nat` addresses, lists, and recursive values keep the semantic
model small; their physical representation has not been chosen here.

## What is proved

`Project/Scheme/VM.lean` states an inductive `Transition` relation separately from
the implementation. Its rules do not use `step`, `execute`, `enter`, `applyProc`, or
`deliver`. They specify fetches, operand arrangements, frame creation/restoration,
and store effects. Closure entry specifies the complete new environment by zipping
parameters with consecutive fresh locations, and the complete new store by appending
arguments in source order. `bind_eq` proves that the binder implements this direct
contract. The rules still share the arithmetic and environment lookup functions with
the implementation.

For every instruction array and states `s`, `t`, the main one-step contract is:

```lean
t.NonError → (step code s = t ↔ Transition code s t)
```

Both directions are needed. Soundness rules out successful behavior contrary to
the rules. Completeness rules out implementing a valid instruction by failing.
`fails_iff_no_transition` additionally proves that a step fails exactly when no
successful rule applies. Exact error labels are checked by the regression programs;
there is no separate inductive specification of the labels.

`Trace code n s t` is a sequence of exactly `n` transitions of that relation. For every
fuel budget, including zero and budgets extending beyond completion:

```lean
t.NonError → (run code n s = t ↔ Trace code n s t)
```

The control and storage laws quantify over arbitrary states and arguments:

| Theorem | Contract |
|---|---|
| `call_depth` | An ordinary call adds exactly one active return frame. |
| `tailcall_frame`, `tailcall_depth` | A tail call retains the exact frame and leaves active return depth unchanged. |
| `tailcall_closure` | Closure entry after the tail call still uses that exact frame. |
| `capture_continuation` | The callback is applied to the saved stack with the same return frame. |
| `invoke_continuation`, `resume_frame` | Invocation restores saved control and retains the invoker's current store. The saved continuation is never consumed. |
| `bind_eq`, `bind_iff` | The complete environment and store have the specified parameter order, fresh locations, and supplied values. |
| `bind_size`, `bind_head` | Successful binding has the correct arity and exact allocation size; the first parameter names its fresh location. |
| `bind_preserves`, `store_other` | Binding keeps every pre-existing location; mutation keeps every other location. |
| `run_add`, `run_error` | Fuel slices compose exactly; failed states remain failed. |
| `Transition.deterministic` | A successful semantic step has a unique result. |

These are source-level VM correctness theorems. They do not prove that a Scheme
compiler preserves expression semantics or that any emitted WASM module implements
this machine.

## Space and WASM boundary

Frame reuse proves the control part of proper tail calls. The store currently grows
on parameter binding and has no collector. The 10,000-call check therefore measures
active return depth, not bounded total memory. It ends with 10,002 retained store
cells: the initial recursive closure and 10,001 parameter bindings, including the
initial call. This implementation does not yet establish Scheme's full space guarantee.

The next VM implementation needs a representation for shared stack roots and store
locations, plus reclamation of unreachable cells. The current LeanExe owned-tree
allocation/release rules are insufficient by themselves for shared continuations
and cycles through store locations. Collection must trace the current control,
environment and stack, including environments and operands in saved continuations,
and any constant model values retained by code. It cannot treat abandoned parameter
cells as permanently live or reuse a location still reachable from a continuation.

Keep the next proof obligation explicit: a representation relation and a simulation
of machine steps by the concrete VM, including allocation failure and collection.
Then use LeanExe's existing per-program `Implements` route to connect that concrete
VM to its WASM artifact. Reader and Scheme compilation can be added after that
boundary is settled.

## Verification and development record

The five new Lean modules were checked directly using the repository's pinned
Lean 4.34.0-rc2 toolchain. The user explicitly authorized direct Lean execution for
this session. No Mathlib or Talos dependencies are needed for these focused checks;
they import only `Std` and the new modules. The full repository build and WASM gates
were not run.

In a normal repository environment, the focused checks are:

```sh
tools/leanrun --timeout 60s lake build LeanExe.Scheme.Examples Project.Scheme.VM Project.Scheme.Tests
tools/leanrun --timeout 60s lake env lean --run Project/Scheme/RunTests.lean
```

There are 27 kernel-reduced program checks, covering argument order, a pending
operand across a call, caller environment restoration, captured-location mutation,
self-recursive tail calls, reuse of an existing caller frame, continuation escape
through nested calls, repeated invocation after the callback returns, primitive
callbacks, truthiness, and malformed code. The larger native
check runs 10,000 tail calls, returns 0, and observes peak active return depth 0.

2026-10-05: The first review removed a boolean-only branch check and used Scheme
truthiness directly. Application and delivery remained separate control states so
primitive callbacks have the same tail behavior as closures. The first instruction
proof passed after making the exhaustive failure cases close without simplifying
the successful cases incidentally; this also removed unused-simp warnings.

The successful-step theorem was extended to exact finite traces and to failure
when no semantic rule is enabled. Generic binding lemmas expose fresh parameter
locations and preservation of old locations. The multi-shot example deliberately
keeps a pending operand below `call/cc` and changes a store counter after capture;
an implementation that consumes the continuation or restores its old store cannot
produce the checked result 102. Kernel reduction required a local recursion-depth
limit of 2048 for this example, without increasing the heartbeat limit or using
native proof evaluation.

The current axiom audit for the tail-call and continuation theorems reports only
`propext`. The main execution and binding lemmas additionally report the usual
`Classical.choice` and `Quot.sound` axioms through the closed-form binder's library lemmas. No new axioms,
`sorry`, `native_decide`, or `bv_decide` are used. The executable step, runner, and
binder also report only `propext`. Root imports include the model, examples, proofs,
and program checks.

## Critical review: remaining obligations

The control model passes the review, but it is an executable specification rather
than the requested WASM VM. The main remaining obstacles are concrete representation
and reclamation. The return-depth theorem does not account for heap retention, and
the observed 10,002-cell store makes that distinction measurable. Do not present this
milestone as a properly tail-recursive Scheme runtime or a verified WASM artifact.

The execution proof establishes agreement with our chosen instruction rules. It is
not an independent derivation of Scheme semantics. The closure rule formerly called
the implementation binder, so a shared bug in argument allocation/order could evade
that rule. The review replaced this premise with the direct environment/store
contract and proved `bind_eq` for all parameters. The size and preservation proofs
now reuse that contract rather than repeating inductions.

`State.NonError` says only that a state is not marked failed. We have not established
a structural invariant saying that every captured environment and saved continuation
has valid locations and a valid stack shape. Checked accesses catch invalid locations,
but that does not establish that valid source programs avoid errors. Before the
concrete representation proof, define and preserve the invariant needed by its
handles and collector; source-language progress additionally needs a compiler proof.

`push Value` permits runtime closures and continuations in instructions. This is
convenient for a semantic API but couples code constants to the store and makes code
a collector root. Before serializing bytecode, decide whether to restrict `push` to
literals/builtin tokens or give a constant pool an explicit representation and root
contract. The future Scheme compiler must also reject duplicate formal names and
preserve the fixed-code-image contract already noted above.

The original tests resumed a continuation after normal return, but never discarded
an ordinary nested caller; the long tail loop ran only at the halt boundary. Two
new programs close those gaps. One returns 107 after a tail chain under a caller with
a pending operand and observes peak depth 1. The other invokes a continuation from
two nested calls, skips the instructions following invocation, returns 107, and
observes peak depth 3 before escape. All four new kernel checks pass.

During this review, rewriting both list-to-array cons and array-push-as-append through
the default simplifier caused a rewrite loop. The closed-form binder proof now uses
`simp only` followed by explicit append rewrites; it checks without increased proof
limits or warnings. The instruction soundness/completeness and trace theorems check
against the stronger closure rule. WASM gates and the full Project build remain
outside the focused validation reported here.
