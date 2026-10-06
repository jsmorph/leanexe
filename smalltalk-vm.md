# Smalltalk VM

The VM and garbage collector are written in Lean and compiled to WebAssembly
by leanexe. JavaScript compiles workspace source, copies the instruction array
into WASM memory, calls the VM, and reads the result. It does not execute the
Smalltalk instructions.

## Run

```sh
tests/smalltalk/run.sh
node tools/smalltalk-run.mjs build/smalltalk/smalltalk.wasm tests/smalltalk/examples/count.st
node tools/smalltalk-run.mjs build/smalltalk/smalltalk.wasm tests/smalltalk/examples/escape.st --stress
```

The driver uses the pinned Lean toolchain through `tools/leanrun`, one process
at a time. Follow `AGENTS.md` for local execution. Node must support WebAssembly.

The CLI accepts `--stress`, `--capacity N`, and `--fuel N`. Capacity and fuel
must be integers from 0 through 18,446,744,073,709,551,615. Unknown options,
missing values, negative values, and values above that range are rejected before
allocation. Capacity
is clamped by the VM to 8 through 1,048,576 cells. Zero fuel executes no
instructions; the CLI reports an unfinished run as `instruction fuel exhausted`.

## Checked results

The full driver passes with Lean 4.34.0-rc2 and Node 24.19.0:

| Check | Result |
|---|---|
| 68 programs with ordinary and stress GC | 136 native executions |
| The same executions in WASM | 136 exact comparisons of the final arena |
| Invalid program headers and method/class records | 14 rejections |
| Failed literal, object, activation, and boot allocation | 4 failures without partial construction |
| Zero fuel followed by split execution | 2 checks, one for each GC mode |
| Mixed heap graphs | 25 checks of reachable cells, free-list membership, and reuse |
| Invalid source | 19 compiler rejections |
| CLI | 2 examples, 8 invalid options, and zero-fuel rejection |

There are 181 WASM checks in total. The CLI examples return 1000 and 42.
A 10,000-iteration loop completes in 24 cells with both GC modes. The comparison
regressions complete in 11 cells; they previously failed because the VM reserved
two cells for an operation that allocated one.

The emitted module is 25,208 bytes and has no imports. Its SHA-256 is
`423aaec2687c65c9993160400cad47efe89f62cfb42d6e2d3095cef90b76b19e`.
The tests check that `boot`, `run`, and `collect` keep the arena address unchanged,
allocate no additional WASM arrays after initialization, and do not grow memory.

## Source compiler and VM support

`tools/smalltalk-compile.mjs` compiles workspace snippets. It accepts signed
64-bit integers, nil, booleans, self, core class names, local declarations,
assignment, parentheses, comments, blocks, block arguments, captured variables,
and `^`. Unary messages are evaluated before binary messages, and binary
messages before keyword messages. Binary messages are evaluated left to right.
Assignment leaves its value. A workspace or block returns its last expression;
an empty body returns nil.

Inside a block, `^` returns from the enclosing method where the block was
written. That method must still be active on the current call chain; otherwise
the VM reports error 7. A block that uses an ordinary return can run after its
enclosing method has returned. Captured variables remain mutable. A block
keeps the activation it captured, so collecting and reusing other cells cannot
turn a completed enclosing method into an active one.

The supplied library implements `new`, `+`, `-`, `<`, `=`, `==`, `value`,
`value:`, `collect`, `ifTrue:`, `ifFalse:`, and `whileTrue:`. The conditional and
loop methods are VM instructions, not host operations. Integer overflow and
wrong arithmetic operand types run the primitive method's instruction fallback;
the supplied fallbacks return nil. Integer identity compares values, class
identity compares represented class IDs, and other identity compares handles.

The VM also supports classes, metaclasses, inherited methods, instance fields,
super sends, and blocks with multiple arguments. These are tested with the
instruction builder in `tools/smalltalk-program.mjs`. The source compiler does
not accept class or method definitions. Its library supplies block calls with
zero or one argument.

Strings, symbols, arrays, arbitrary-size integers, reflection, processes,
Smalltalk images, and graphics are not implemented. There is no tail-call
optimization. No CSOM or PySOM compiler adapter is implemented; see
[smalltalk-compilers.md](smalltalk-compilers.md).

## Program and entry points

Use `init`, `boot`, `run`, `step`, `collect`, and `resultWord`. The other exported
functions are implementation helpers with unchecked preconditions. Forged
pointers and arbitrary arena contents are not supported inputs.

Keep the program unchanged during execution, and use the same program for every
call on an arena. `boot` requires a fresh arena. `run` executes at most its fuel
count of instructions and returns the arena even if execution is unfinished.
It can be called again to continue. `step` and `run` leave finished and failed
states unchanged. Collection leaves failed states unchanged.

The program is an array of UInt64 words. Class and method IDs start at 1.
Instruction positions (PCs) start at 0. The eight-word header is:

| Word | Meaning |
|---|---|
| 0, 1, 2 | Class, method, instruction counts |
| 3 | Entry method ID |
| 4, 5, 6, 7 | Nil, boolean, integer, block class IDs |

A class record has four words: parent ID, metaclass ID, total field count, zero.
A parent ID is zero or smaller than its child's ID. Field counts include
inherited fields and cannot decrease from parent to child. Metaclass IDs must
name classes; metaclass links may cycle.

A method record has six words: defining class ID, selector ID, argument count
including self, local count, entry PC, primitive ID. Blocks have selector zero.
The entry method has a nonzero selector and argument count one. Counts and field
or local sizes are bounded by 1,048,576; class, method, instruction, and argument
counts must be positive. `boot` checks these records and the exact array length:
`8 + 4 * classes + 6 * methods + 4 * instructions`.

Each instruction has four words: opcode, operand a, operand b, zero. Unused
operands must be zero. `step` checks the current instruction; `boot` does not
validate all instructions. Methods record an entry PC, not a body length.
Jumps use the global instruction table. The compiler or builder must emit
returns to end methods.

| Opcode | Operation | Operands |
|---|---|---|
| 0 | Integer literal | a: 64-bit value |
| 1 | Nil, false, true | a: 0, 1, 2 |
| 2, 3 | Load, store variable | a: slot index; b: enclosing-block depth |
| 4, 5 | Load, store instance field | a: field index |
| 6, 7 | Create block, class value | a: method ID, class ID |
| 8, 9 | Duplicate, pop | None |
| 10, 11 | Send, super send | a: selector ID; b: argument count excluding self |
| 12, 13 | Local, non-local return | None |
| 14, 15 | Jump, branch on false | a: absolute PC |

Slot zero is self; arguments and locals follow. A super send starts at the
parent of the method's defining class. A block retains that defining class.
Primitive IDs are: 0 instruction body; 1 new; 2 add; 3 subtract; 4 less-than;
5 numeric equality; 6 identity; 7 block call; 8 collect.

A JavaScript call returns an `i64` as a signed BigInt. Use `BigInt.asUintN(64, x)`
for a UInt64 comparison or `BigInt.asIntN(64, x)` to display an integer result.

## Heap and collection

One arena array contains 24 register words, eight words per cell, and one
worklist word per cell: `24 + 9 * capacity` words. Handles are cell indices.
Handle zero means absent. Handles 1, 2, and 3 are permanent nil, false, and true.

A cell contains kind, mark, and six payload words a through f:

| Kind | Payload | Fields holding handles |
|---|---|---|
| 1 | Integer value | None |
| 2 | Nil or boolean value | None |
| 4 | Class ID, field list, metaclass ID | b |
| 5 | Method ID, PC, caller, enclosing activation, slots, operands | c, d, e, f |
| 6 | Block method ID, captured activation | b |
| 7 | Variable or operand value, next link | a, b |
| 8 | Represented class ID, metaclass ID | None |

Collection starts from nil, false, true, the current activation, the result,
and external-root register 16. It follows only the handle fields in the table;
class IDs, method IDs, PCs, and integer values are not references. A cell is
marked before entering the worklist, so it enters at most once. Sweep clears
unmarked cells and rebuilds the free list. It reclaims unreachable cycles,
keeps live cells at their existing indices, and allocates no second heap.

Each allocating instruction reserves all the cells it needs before changing
roots. Collection can happen during reservation, but not during construction.
Register 19 holds a temporary list during construction and is cleared before
the instruction returns. No partially constructed object or activation is
installed when reservation fails. Reservation is conservative: cells made
unreachable later in the instruction are still considered live during its check.

Retiring an activation clears its caller and operands and marks its PC as
completed. It retains its enclosing activation and variable slots for blocks
that captured it.

Registers: 0 phase; 2 current activation; 7 result; 8 free-list head; 9 free count;
10 last allocation; 11 collection count; 12 stress flag; 13 peak cell use;
14 capacity; 15 error; 16 external root; 17 allocation count; 18 worklist count;
19 construction list. Other registers are unused. Phase 0 runs, 3 finishes,
and 4 fails. Stress mode collects before each allocating instruction and during
boot.

Errors: 1 invalid PC or activation; 2 invalid variable/field slot; 3 corrupt
heap during collection; 4 operand stack underflow; 5 missing method; 6 wrong
argument count; 7 invalid non-local return; 8 non-boolean condition; 9 out of
memory; 10 invalid program or instruction.

## Proofs and remaining limits

`Project/Smalltalk/Memory.lean` proves read-after-write, unchanged reads at other
indices, cell address bounds without integer wraparound, and separation between
registers and cells. `Shape` requires capacity 8 through 1,048,576, exactly
`24 + 9 * capacity` words, and register 14 equal to capacity. `Handle` requires
a cell index from 1 through capacity.

`Project/Smalltalk/Allocation.lean` proves the complete word-level effect of
the concrete `Arena.allocateCell`, the contents of its new cell, preservation
of every other cell, and preservation of arena shape. These theorems require
`Shape` and a valid free-head handle.

`Project/Smalltalk/FreeList.lean` defines a valid free list using the array's
actual head, count, cell tags, and next words. Its handles are distinct, within
capacity, and contain exactly the zero-tagged cells. `allocate_valid` proves
that allocating a nonzero tag from a nonempty valid list removes exactly its
head, preserves the remaining order, decrements the count once, and preserves
arena shape and list validity. `allocate_empty_preserves_cells` proves that
an empty valid list produces error 9 without changing any cell.

`Project/Smalltalk/Sweep.lean` proves that the concrete `finishCollection`
preserves every word of every marked cell. `Project/Smalltalk/SweepList.lean`
proves that its rebuilt free list contains exactly the unmarked handles,
without duplicates, with the correct count. These results require `Shape`;
the list result also requires nonzero tags on marked cells. They allow any
contents in unmarked cells and any old free-list order. They do not yet prove
that marking identifies exactly the reachable cells.

`Project/Smalltalk/Clear.lean` proves that the actual clearing loop zeroes every
mark and preserves payloads, registers, and arena shape. `MarkMemory.lean`
checks enqueue's exact writes, worklist bounds, unchanged payloads, and the
existing-mark and new-mark branches. The new-mark result assumes worklist space.

`Project/Smalltalk/Graph.lean` defines reachability from the six roots through
the pointer fields listed above. `sweep_correct` connects the concrete sweep
to that definition: given exact marking, it preserves reachable payloads and
builds a valid free list containing exactly the unreachable handles. This is
conditional on exact marking; the complete marking theorem supplies that
condition under the valid-heap assumptions below.

`Project/Smalltalk/Worklist.lean` relates the actual worklist words and count
to a list of handles. `MarkInvariant.lean` proves that checked `mark` either
keeps that list or appends one reachable handle. Its invariant relates actual
mark words to the scanned and pending handles and excludes duplicates. From
distinct valid handles, `mark_holds` derives worklist space for a new handle.
The clearing and root-marking results establish the basic invariant and cover
all six roots. `ScanMemory.lean` proves that `scanCell` pops the represented top
handle and marks exactly its pointer fields. `ScanInvariant.lean` proves that
a scan preserves the basic invariant, moves one distinct handle to the scanned
list, and closes its outgoing edges. Closure is stated separately because
the edges are still being marked between pop and the end of a scan. Cycles and
repeated pointers are allowed. `Marking.lean` proves that the actual bounded
scan loop finishes within capacity and marks exactly the reachable handles.

`Project/Smalltalk/Collector.lean` proves `collect_correct` for the actual
`Arena.collect`: arena shape is preserved, every reachable cell keeps its
handle, tag, and payload words, and the rebuilt free list contains exactly
the unreachable handles, without duplicates, with the correct count.
`collect_register` proves that registers other than 8, 9, 10, 11, and 18 are
unchanged. `collect_error_unchanged` checks the already-error case.

The collector theorem assumes `Graph.Valid`: valid arena shape; every nonzero
root names an allocated valid handle; every pointer from an allocated cell
names an allocated valid handle or zero; and every allocated cell has one of
the supported tags. It also assumes phase is not 4. It allows cycles, repeated
pointers, arbitrary initial marks, and any old free-list order. It does not
assume marking is correct, spare worklist space, or a valid old free list.

`Project/Smalltalk/Frame.lean` checks the concrete frame writes. Retirement
sets the PC to dead, clears caller and operands, and preserves the remaining
fields, other cells, registers, and arena shape. Advance increments the PC,
replaces operands, and preserves all other cell words and registers.
`Traversal.lean` proves that concrete `walk` and `lexical` return the selected
handle from a represented path, or zero after its end, using the actual
capacity-clamped traversal count.

`Project/Smalltalk/Execution.lean` proves that `run` performs the stated number
of steps with finished and error states absorbing. `run_resume` proves that
two successive runs agree with their combined fuel when the sum is below
2^64. This is a fuel theorem; it does not specify individual instructions.

`tests/smalltalk/proofs.lean` checks every theorem in `Project.Smalltalk`,
including its dependencies, and permits only Lean's standard axioms
`propext`, `Quot.sound`, and `Classical.choice`. It rejects admitted proofs and
additional axioms. The test driver runs this check. The proof journal is
`smalltalk-proof-journal.md`.

`LeanExe/Smalltalk/Control.lean` defines separate list models for first-method
lookup, inherited lookup with a limit, and return through a live method
activation. `Project/Smalltalk/Control.lean` proves that those functions match
their stated rules, give only one result for the same input, and retire exactly
the calls through the return target. An axiom audit of the main lookup and return
laws reports only `propext`; the completed-first-frame rejection law uses none.

The list-model proofs do not refer to `Runtime.lookup` or `Runtime.ret`.
There is no theorem connecting the concrete VM to those models,
no complete VM instruction correctness theorem, no source compiler correctness theorem, and
no proof of the emitted WASM module. The checks above are execution tests.

Lookup runs its full `classes * (methods + 1)` loop even after finding a method.
Home and call-chain searches run their full capacity bound. Fuel counts VM
instructions and does not separately limit these scans; one instruction can
perform a large scan. These searches need early stopping before scaling to
large programs.
