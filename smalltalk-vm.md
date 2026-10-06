# Smalltalk VM

This branch reconstructs the Smalltalk development lost during workspace cleanup.
The VM and nonmoving GC are Lean functions compiled by leanexe to WebAssembly.
`tools/smalltalk-compile.mjs` is a temporary source compiler for workspace snippets.
The host allocates the input and arena arrays; execution stays inside WASM.

Reconstruction is in progress. The control proofs pass Lean checking, and all
59 programs pass natively with both ordinary and stress GC: 118 runs. This
includes a 10,000-iteration VM loop in 24 cells. The compiler rejects 19 invalid
source inputs. WASM compilation and execution remain pending. The branch is
committed and pushed in checkpoints; measured WASM results will be added after
the full driver passes.

## Run

```sh
tests/smalltalk/run.sh
node tools/smalltalk-run.mjs build/smalltalk/smalltalk.wasm tests/smalltalk/examples/count.st
node tools/smalltalk-run.mjs build/smalltalk/smalltalk.wasm tests/smalltalk/examples/escape.st --stress
```

Every Lean/Lake process runs through `tools/leanrun`, serially. Local mode may be
used only with the user's explicit authorization, as specified in `AGENTS.md`.
The host requires Node with WebAssembly support. There is no Rust implementation.

The driver creates the corpus, checks compiler rejection cases, builds the Lean
proofs and native runner, emits and decodes the WASM, and compares every resulting
arena word with native Lean. Each program runs with ordinary and stress GC.
The JS test also checks collection against an independent graph reachability
oracle, stable arena addresses, host allocation accounting, and absorbing error
and finished states.

## Supported language and VM

The VM supports class and metaclass tables, inherited lookup, receiver fields,
ordinary sends, lexical super sends, local variables, captured mutable slots,
blocks with arguments, local returns, and non-local returns. Anonymous block
descriptors retain their lexical defining class, including for super sends.

An ordinary escaped block can execute after its home returns. A non-local return
requires its home activation to be live on the current dynamic chain; otherwise
it reports error 7. Retiring an activation clears its dynamic caller and operand
stack but preserves its lexical parent and slots. Blocks retain the home object
itself, preventing a reused heap handle from reviving an expired home.

Integer primitives use signed 64-bit values. Overflow and wrong operand types
execute the primitive method's bytecode fallback; the minimal library returns
nil. Identity compares integer values and represented class IDs, and otherwise
uses stable object handles. Nil and booleans are canonical objects.

The temporary compiler supports integers, nil/booleans, self, core class globals,
local declarations, assignment, parentheses, message precedence, blocks,
arguments, captured locals, comments, and `^`. Assignments leave their value.
Workspaces and blocks return their last expression; an empty body returns nil.
The library provides zero- and one-argument block calls, allocation, arithmetic,
identity, explicit collection, conditionals, and `whileTrue:`. Control methods
are ordinary VM bytecode.

Source class/method files, cascades, strings, symbols, arrays, large integers,
reflection, processes, images, and graphics are outside this first subset.
The assembler exercises classes, fields, metaclasses, inheritance, and super
sends directly. There is no tail-call optimization: block home identity matters.

## Immutable program format

The borrowed program is an array of UInt64 words. IDs start at 1; PCs start at 0.
Its eight-word header is:

| Word | Meaning |
|---|---|
| 0–2 | Class, method, instruction counts |
| 3 | Entry method ID |
| 4–7 | Nil, boolean, integer, block class IDs |

Each class has four words: parent ID, metaclass ID, total inherited field count,
and zero. Parent IDs are smaller than child IDs; metaclass links may cycle.
Each method has six: lexical owner class, selector ID, arity including self,
local count, entry PC, primitive ID. A block has selector 0. Each instruction
has four: opcode, operands a and b, and zero.

| Opcode | Operation |
|---|---|
| 0 | Integer literal |
| 1 | Nil/false/true, operand 0/1/2 |
| 2, 3 | Load/store slot: index and lexical depth |
| 4, 5 | Load/store receiver field |
| 6, 7 | Block descriptor/class literal |
| 8, 9 | Duplicate/pop |
| 10, 11 | Send/super send: selector and argument count excluding self |
| 12, 13 | Local/non-local return |
| 14, 15 | Jump/branch on false to absolute PC |

`boot` validates the exact program size, count bounds, hierarchy, metaclasses,
method descriptors, and entry arity. Execution validates instruction operands.
The host must keep the program immutable and pair an arena with the same program.
Internal helpers are exported by leanexe and are trusted implementation entry
points; arbitrary forged pointers and arenas are not a supported FFI.

## Heap and GC

The arena contains 24 register words, eight words per cell, and one mark-worklist
word per cell: `24 + 9 * capacity`. Capacity is clamped to 8…1,048,576. Handles
1, 2, and 3 are permanent nil, false, and true. Handle 0 means absent.

Each cell contains kind, mark, and six payload words a…f.

| Kind | Payload | Traced fields |
|---|---|---|
| 1 | Integer word | None |
| 2 | Nil/bool value | None |
| 4 | Class ID, field list | b |
| 5 | Method, PC, caller, lexical parent, slots, operands | c, d, e, f |
| 6 | Block method, captured activation | b |
| 7 | Slot/operand value, next link | a, b |
| 8 | Represented class, metaclass | None |

The roots are the three canonical objects, current activation, final result,
and external-root register 16. Registers 19–23 are construction scratch and are
empty at collection safepoints. The collector marks before enqueueing, so each
cell is queued and scanned at most once. Sweep rebuilds the free list and
reclaims dead cycles. It does not move cells or allocate a second heap.

Every allocating transition reserves its whole allocation before changing roots.
No GC occurs during construction. Out of memory installs no partial object or
activation. Reservation is conservative: it may fail even when retiring a frame
first would release enough space.

Registers include phase (0), current activation (2), result (7), free-list head
and count (8–9), last allocation (10), GC count (11), stress flag (12), peak live
cells (13), capacity (14), error (15), external root (16), allocation count (17),
and worklist count (18). Phase 0 runs, 3 finishes, and 4 fails. Fuel exhaustion
leaves a resumable running state; the CLI reports it as an error.

Errors: 1 bad PC/activation; 2 bad slot; 3 corrupt heap/GC; 4 stack underflow;
5 missing selector; 6 arity; 7 invalid non-local return; 8 non-boolean branch;
9 out of memory; 10 invalid program/instruction. Finished and failed VM states
are absorbing. Collection preserves failures.

## Proof boundary

`LeanExe/Smalltalk/Control.lean` specifies first-method lookup, bounded inherited
lookup, and live-home unwinding. `Project/Smalltalk/Control.lean` relates the
functions to inductive specifications and states determinism and retirement
laws. These declarations pass Lean checking.

There is no complete concrete VM/GC refinement theorem or frontend correctness
theorem. This iteration tests the emitted WASM; it does not prove a WASM artifact
theorem. Existing Smalltalk image compatibility remains outside scope.
