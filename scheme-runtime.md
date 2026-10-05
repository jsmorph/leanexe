# Concrete Scheme VM and garbage collection

This runtime is a separate executable implementation of the abstract machine in
`LeanExe/Scheme/VM.lean`. It uses the same calling convention and control behavior,
with an explicit heap for mutable bindings, closures, stacks, and continuations.
`tools/scheme-compile.scm` supplies a small Scheme frontend for exercising it;
see [scheme-compiler.md](scheme-compiler.md). The separate test assembler also
builds direct bytecode fixtures, including malformed programs.

## Representation

`LeanExe/Scheme/Arena.lean` uses one owned `Array UInt64`. Its first 24 words are VM
registers, followed by fixed-size cells of five words and a worklist with one word
per cell. A handle is a cell index from 1 through capacity; zero means an empty
environment or the halt stack. A word value is boxed, so every UInt64 bit pattern
remains usable. Four permanent cells hold false, true, unit, and the call/cc primitive.
The capacity is fixed at initialization, with a minimum of 8 and maximum of 1,048,576.
An arena with 32 cells occupies 216 words (1,728 bytes), before the LeanExe array header.

Each cell is `[kind, mark, a, b, c]`:

| Kind | a | b | c | Traced fields |
|---|---|---|---|---|
| Free | Free-list link | 0 | 0 | None |
| Word | UInt64 payload | 0 | 0 | None |
| Boolean | 0 or 1 | 0 | 0 | None |
| Unit / callcc | 0 | 0 | 0 | None |
| Closure | Entry PC | Descriptor offset | Environment | c |
| Continuation | Saved stack | 0 | 0 | a |
| Operand | Value | Next stack | 0 | a, b |
| Return frame | Return PC | Environment | Rest stack | b, c |
| Environment binding | Symbol | Location | Next binding | b, c |
| Mutable location | Value | 0 | 0 | a |

Environments and stacks are immutable linked cells. Mutation updates location
cells only. Closure descriptors list the names to capture explicitly, and closure
creation builds an environment containing those names while sharing their existing
locations. This prevents a closure from retaining unrelated bindings. Saved
continuations share immutable stack cells; they can be invoked repeatedly and see
the current contents of mutable locations.

## Collection and allocation

The collector is stop-the-world, non-moving mark/sweep. Handles remain stable, so
there is no pointer rewriting. It clears marks, marks the roots, scans the
preallocated worklist, then rebuilds the free list from unmarked cells. Marking
occurs before enqueueing, so a cell enters the worklist at most once, including in
cyclic graphs. At most capacity scans are needed. Collection allocates no memory.
Unreachable cycles are reclaimed. Scalars such as names, PCs, and boxed numbers
are never interpreted as references.

Roots are the four permanent values, the current environment, current stack, and
persistent globals. Application adds its procedure and argument chain. Returning
and done states add their result. Stack traversal reaches suspended environments
and operands; continuation traversal reaches the entire saved stack. Inactive
registers, the last-allocation diagnostic, worklist residue, and scratch registers
are not roots. A completed result remains rooted until the host replaces the state.

Before an allocating VM transition, `reserve` requests its whole allocation budget.
It collects if there is insufficient room, then returns an explicit out-of-memory
state if collection cannot make enough room. The transition performs no allocations
before reservation succeeds. Collection never occurs midway through capture or
parameter binding, so intermediate handles need no extra root protocol. Scratch
registers 19 and 20 exist only inside those reserved transitions and are cleared
before control returns. A stress flag collects before every allocating transition.

| Transition | Maximum cells reserved |
|---|---:|
| Push word / arithmetic | 2 |
| Push canonical value / load / store / comparison / deliver return | 1 |
| Make closure with k captures | k + 2 |
| Ordinary call | 1 |
| Apply closure with n parameters | 2n |
| Apply call/cc | 2 |
| Initialize global binding | 3 |
| Tail call / continuation invocation / branch / drop / return | 0 |

The current environment is cleared on application. A tail call reuses its existing
return boundary, allowing previous parameter locations and operands to become
unreachable. Escaping closures or captured continuations retain the cells they
actually need. Legitimately retained data can exhaust the fixed arena; the runtime
does not grow it. Globals are explicit persistent roots and should be initialized
once, then updated with store instructions.

## Bytecode and host interface

`LeanExe/Scheme/Runtime.lean` implements exec, apply, returning, done, and error as
explicit phases. Execution uses a bounded LeanExe loop; Scheme calls do not recurse
on the Lean or WASM call stack. Code is a word array containing an instruction count,
four words per instruction, then closure descriptors. A descriptor contains arity,
formal names, capture count, and capture names. Opcodes are documented in the source
and assembled in `tests/scheme/corpus.mjs`.

Code arrays stay borrowed; the state array is consumed and returned by each step,
run, or collection. Use the returned state pointer. The module contains LeanExe's
ordinary alloc/release functions for these two outer arrays; Scheme's shared and
cyclic objects live inside the arena and use this collector. Host-held Scheme
handles are not additional roots. Keep a value in globals or another VM root before
collecting. Raw arena helpers are exported for tests, not a protected embedding API.
Keep the code array alive and unchanged while its closures or continuations can run.

Errors are terminal and retain their reason: bad PC=1, unbound name=2, corrupt heap=3,
underflow=4, expected words=5, expected return boundary=6, not callable=7, arity=8,
out of memory=9, malformed code=10. Fuel exhaustion leaves a resumable active state.

## Verification

Run `SCHEME=chibi-scheme tests/scheme/run.sh` in a configured repository environment. It builds the
compiled module and native executable, emits the WASM through the existing encoder,
and executes that binary with Node's WebAssembly API. The shared corpus tests normal
and forced collection. Native snapshots allow comparison of every register, cell,
and worklist word, rather than only the returned number. The WASM suite also checks
free-list integrity and graph reachability, cycles, scalar fields that resemble
handles, repeated invocation after explicit collection, and bounded physical arena
use. Shorter programs are inspected after every transition.

No WASM artifact proofs are part of this development. The old abstract-machine theorems
remain separate; a simulation between that model and this arena implementation has
not been proved. The implementation and tests target this small VM, including its
UInt64 arithmetic, rather than a complete Scheme language.

## Development record

2026-10-05: Kept one flat word array rather than adding a shared-reference scheme to
LeanExe's owned tree allocator. Fixed-size cells avoid variable-size allocation and
compaction. Reserving an entire transition makes the rooting discipline explicit
without requiring a general root stack. Explicit closure capture descriptors were
needed so unrelated parameter locations can die during tail recursion.

The first 54 native runs passed. A 10,000-call countdown completed in a 32-cell arena;
forced collection peaked at 17 cells. The malformed-descriptor case exposed a noisy
native out-of-bounds read, despite returning the expected error. Moved descriptor
validation before that read. The small word-array access helpers are inline, so
scalar loops use direct reads rather than unsupported borrowed-array calls. The pinned compiler imports
existing WASM support lemmas, so their dependencies must build before emission; no
new artifact proof was requested or attempted.

The first compiler build crashed with exit code 139 in the pinned dependency's
`CodeLib.RustStd.Frame`, a Lean file of memory lemmas. Its import came from
`Project/TalosPrelude.lean`. Removed that import, retained its existing `rfl`
memory-size identity locally, and removed two now-unneeded simp-attribute overrides.
The compiler already uses the project's kernel-checked word round-trip rule.
Also narrowed the imports in CallRemainder and Aborts to their direct interpreter
dependencies. No Rust toolchain is used by the Scheme implementation or tests.

The GC alone emitted a 6,338-byte module and passed rooted/dead cycle checks on
actual WASM. The combined VM/GC emitted 20,288 bytes, with no imports. Its original
bytecode suite passed 81 checks, including 58 comparisons of every arena word with
native Lean. The WASM countdown completed 10,000 tail calls in 32 cells. Runs used
the same state buffer throughout, made no outer allocator calls during execution,
and did not grow linear memory. Array-carrying loops use the compiler's existing
pair-state `repeatWhile`; checks and straight-line allocating workers keep array
bindings within the compiler's supported fragment.

The complete `tests/scheme/run.sh` subsequently passed with the Scheme frontend:
27 source programs compiled, 22 unsupported/malformed programs rejected, 112 native
executions, and 159 WASM checks including 112 complete arena comparisons. It also
rebuilt the abstract VM's soundness/completeness development and 27 kernel-reduced
example theorems, and ran its separate 10,000-tail-call audit. Compiled source tests
cover first-class primitives, transitive closure captures, lexical mutation,
mutual recursion, both branch paths, and multi-shot continuations. The standalone
runner returned 7, 102, 123, and 0 for countdown, multi-shot, first-class addition,
and UInt64 wraparound respectively.
